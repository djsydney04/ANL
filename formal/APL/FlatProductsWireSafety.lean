import APL.FlatProductsWire
import APL.FlatProductsSafety

namespace APL.FlatProductsWire
open Lean FlatProducts
open Wire (Decode field needSome)

/-- Typing premises for the existing expression and nullary program entry forms. -/
inductive InputTyped : Input → FlatProducts.Ty → Prop where
  | expression : FlatProducts.HasType #[] [] e t → InputTyped (.expression e) t
  | program : WellTyped fs → fs[entry]? = some fn → fn.params = [] →
      fn.result = .scalar .i64 → InputTyped (.program fs entry) (.scalar .i64)

private theorem bind_ok {x : Except ε α} {f : α → Except ε β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

private theorem mapM_member {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) (hy : y ∈ ys) : ∃ x, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    change Except.ok [] = Except.ok ys at h
    cases h
    simp at hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_ok] at h
    obtain ⟨v, hv, tail, ht, final⟩ := h
    change Except.ok (v :: tail) = Except.ok ys at final
    cases final
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, hv⟩
    · exact ih ht hy

private theorem mapM_agree {f : α → Except ε β} {g : α → Except ε γ}
    {xs : List α} {ys : List β} {zs : List γ} {p : β → δ} {q : γ → δ}
    (hf : xs.mapM f = .ok ys) (hg : xs.mapM g = .ok zs)
    (same : ∀ x y z, f x = .ok y → g x = .ok z → p y = q z) :
    ys.map p = zs.map q := by
  induction xs generalizing ys zs with
  | nil =>
    change Except.ok [] = Except.ok ys at hf
    change Except.ok [] = Except.ok zs at hg
    cases hf; cases hg; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_ok] at hf hg
    obtain ⟨y, hy, yt, hyt, yf⟩ := hf
    obtain ⟨z, hz, zt, hzt, zf⟩ := hg
    change Except.ok (y :: yt) = Except.ok ys at yf
    change Except.ok (z :: zt) = Except.ok zs at zf
    cases yf; cases zf
    simp only [List.map_cons, same x y z hy hz, ih hyt hzt]

-- A proof-local name for the unchanged second-pass action in `document`.
private def readFunction (sigs : Signatures) (item : Json × Nat) : Decode Function := do
  let (j, i) := item
  let (name, params, result) ← signature i j
  let context := immutable params.reverse
  let (body, actual) ← term sigs 128 context (← field j "body")
  if actual ≠ result then throw "function result mismatch"
  if FlatProducts.infer sigs context body ≠ some result then throw "program checker disagreement"
  pure ({ name, params, result, body } : Function)

private theorem readFunction_checked {sigs : Signatures} {item : Json × Nat} {fn : Function}
    (h : readFunction sigs item = .ok fn) :
    signature item.2 item.1 = .ok (fn.name, fn.params, fn.result) ∧
    FlatProducts.infer sigs (immutable fn.params.reverse) fn.body = some fn.result := by
  rcases item with ⟨j, i⟩
  unfold readFunction at h
  simp only [bind_ok] at h
  rcases h with ⟨⟨name, params, result⟩, hs, raw, hr, ⟨body, actual⟩, hb, h⟩
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨hs, by simpa only [ne_eq, Decidable.not_not] using ‹¬ FlatProducts.infer sigs (immutable params.reverse) body ≠ some result›⟩

private theorem tables_checked {items : List (Json × Nat)}
    {named : List (String × (List FlatProducts.Ty × FlatProducts.Ty))}
    {fs : List Function}
    (hs : items.mapM (fun (j, i) => signature i j) = .ok named)
    (hf : items.mapM (readFunction (named.map Prod.snd).toArray) = .ok fs) :
    WellTyped fs.toArray := by
  have aligned : named.map Prod.snd = fs.map (fun fn => (fn.params, fn.result)) :=
    mapM_agree hs hf (fun item _ fn hs hf => by
      rcases item with ⟨j, i⟩
      have fields := (readFunction_checked hf).1
      change signature i j = .ok _ at hs
      rw [hs] at fields
      cases fields
      rfl)
  have sigs : (named.map Prod.snd).toArray = signatures fs.toArray := by
    simpa only [signatures, List.map_toArray] using congrArg List.toArray aligned
  apply checked_functions
  intro i fn hi
  have member : fn ∈ fs := List.mem_of_getElem? (by simpa using hi)
  obtain ⟨item, hitem⟩ := mapM_member hf member
  simpa only [sigs] using (readFunction_checked hitem).2

theorem document_typed {j : Json} {input : Input}
    (h : document j = .ok input) : ∃ t, InputTyped input t := by
  unfold document at h
  simp only [bind_ok] at h
  rcases h with ⟨revisionJson, hrj, revision, hr, h⟩
  split at h
  · cases h
  · simp only [bind_ok] at h
    rcases h with ⟨schemaJson, hsj, schema, hs, h⟩
    split at h
    · simp only [bind_ok] at h
      rcases h with ⟨_, _, raw, _, ⟨e, t⟩, _, h⟩
      split at h
      · cases h
      · rename_i checked
        cases h
        exact ⟨t, .expression (FlatProducts.infer_sound (Decidable.not_not.mp checked))⟩
    · simp only [bind_ok] at h
      rcases h with ⟨_, _, raw, _, functions, _, named, hn, h⟩
      split at h
      · cases h
      · simp only [bind_ok] at h
        rcases h with ⟨fs, hf, entryJson, _, entry, _, main, hm, h⟩
        change functions.toList.zipIdx.mapM (readFunction (named.map Prod.snd).toArray) = .ok fs at hf
        split at h
        · cases h
        · rename_i valid
          cases h
          have lookup : fs[entry]? = some main := by
            cases he : fs[entry]? with
            | none => simp [needSome, he] at hm
            | some fn => simp only [needSome, he, Except.ok.injEq] at hm; subst fn; rfl
          have shape : main.params = [] ∧ main.result = .scalar .i64 := by
            simpa only [not_or, ne_eq, Decidable.not_not] using valid
          exact ⟨.scalar .i64, .program (tables_checked hn hf)
            (by simpa using lookup) shape.1 shape.2⟩
    · cases h

/-- Successful decoding supplies typing premises, without a textual parsing equivalence claim. -/
theorem decode_typed {text : String} {input : Input}
    (h : decode text = .ok input) : ∃ t, InputTyped input t := by
  unfold decode at h
  split at h
  · cases h
  · simp only [bind_ok] at h
    obtain ⟨_, _, json, _, accepted⟩ := h
    exact document_typed accepted

theorem document_program_typed {j : Json} {fs : Functions} {entry : Nat}
    (h : document j = .ok (.program fs entry)) :
    WellTyped fs ∧ ∃ fn, fs[entry]? = some fn ∧ fn.params = [] ∧ fn.result = .scalar .i64 := by
  obtain ⟨t, typed⟩ := document_typed h
  cases typed with
  | program wf lookup arity result => exact ⟨wf, _, lookup, arity, result⟩

theorem decode_program_typed {text : String} {fs : Functions} {entry : Nat}
    (h : decode text = .ok (.program fs entry)) :
    WellTyped fs ∧ ∃ fn, fs[entry]? = some fn ∧ fn.params = [] ∧ fn.result = .scalar .i64 := by
  obtain ⟨t, typed⟩ := decode_typed h
  cases typed with
  | program wf lookup arity result => exact ⟨wf, _, lookup, arity, result⟩

/-- Defined traps and exhausted fuel remain permitted outcomes. -/
def ResultTyped (t : FlatProducts.Ty) : Except Program.Error FlatProducts.Val → Prop
  | .ok v => v.type = t
  | .error (.trap _) | .error .resourceLimit => True
  | .error .invalid => False

private theorem run_result_typed {fs : Functions} {initial : FlatProducts.State}
    (wf : WellTyped fs) (typed : initial.Typed (signatures fs) t) :
    ResultTyped t (match FlatProducts.run fs fuel initial with
      | some (.ret v _ []) => .ok v
      | some (.trap kind) => .error (.trap kind)
      | none => .error .resourceLimit
      | _ => .error .invalid) := by
  cases hr : FlatProducts.run fs fuel initial with
  | none => trivial
  | some last =>
    rcases FlatProducts.finite_run_safe wf typed hr with value | trap
    · obtain ⟨v, env, rfl, ht⟩ := value
      exact ht
    · obtain ⟨kind, rfl⟩ := trap
      trivial

theorem execute_typed {input : Input} {t : FlatProducts.Ty}
    (h : InputTyped input t) (fuel : Nat) : ResultTyped t (execute input fuel) := by
  cases h with
  | @expression e t ht =>
    have wf : WellTyped (#[] : Functions) := by
      intro i fn hi
      simp at hi
    have initial : FlatProducts.State.Typed (signatures #[]) (.eval e [] []) t :=
      .eval (Γ := []) (by simpa only [signatures, Array.map_empty] using ht) rfl .nil
    exact run_result_typed wf initial
  | program wf lookup arity result =>
    have initial := FlatProducts.entry_typed lookup arity
    rw [result] at initial
    exact run_result_typed wf initial

theorem execute_no_invalid {input : Input} {t : FlatProducts.Ty}
    (h : InputTyped input t) (fuel : Nat) : execute input fuel ≠ .error .invalid := by
  intro invalid
  have safe := execute_typed h fuel
  rw [invalid] at safe
  exact safe

theorem execute_value_type {input : Input} {t : FlatProducts.Ty} {fuel : Nat}
    (h : InputTyped input t) (value : FlatProducts.Val)
    (returned : execute input fuel = .ok value) : value.type = t := by
  have safe := execute_typed h fuel
  rw [returned] at safe
  exact safe

theorem decoded_execute_safe {text : String} {input : Input}
    (h : decode text = .ok input) :
    ∃ t, InputTyped input t ∧ ∀ fuel,
      execute input fuel ≠ .error .invalid ∧
      ∀ value, execute input fuel = .ok value → value.type = t := by
  obtain ⟨t, typed⟩ := decode_typed h
  exact ⟨t, typed, fun fuel => ⟨execute_no_invalid typed fuel, execute_value_type typed⟩⟩

end APL.FlatProductsWire
