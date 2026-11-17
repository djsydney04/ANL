import ANL.MemoryLoweringSupport

namespace ANL.Memory.Lowering

private theorem logical_types (h : APL.FlatProducts.binaryType op u v = some t)
    (hop : op = .and ∨ op = .or) :
    u = .scalar .bool ∧ v = .scalar .bool ∧ t = .scalar .bool := by
  rcases hop with rfl | rfl <;>
    cases u with
    | scalar ut =>
        cases v with
        | scalar vt => cases ut <;> cases vt <;> simp_all [APL.FlatProducts.binaryType, APL.binaryType]
        | tuple shape => simp [APL.FlatProducts.binaryType] at h
    | tuple shape => cases v <;> simp_all [APL.FlatProducts.binaryType]

theorem term_typed (offset : Nat) (h : HasType sigs Γ R e t) :
    ∀ c locals resources supply, Represented c locals resources Γ R →
      ∃ result next, term offset locals resources e supply = some (result, next) ∧ result.Typed sigs c t := by
  induction h using HasType.rec
    (motive_2 := fun Γ R es ts _ =>
      ∀ c locals resources supply, Represented c locals resources Γ R →
        ∃ result next, arguments offset locals resources es supply = some (result, next) ∧
          result.Typed sigs c ts) with
  | @lit Γ R v =>
      intro c locals resources supply rep
      simp only [term]
      refine ⟨_, _, rfl, emit_typed trivial ?_⟩
      cases v <;> rfl
  | @«local» Γ index t permission R hi =>
      intro c locals resources supply rep
      obtain ⟨l, hl, ht, visible⟩ := rep.local_lookup hi
      cases l with
      | value value =>
          cases ht
          simp only [term, hl, bind, Option.bind_some]
          exact ⟨_, _, rfl, trivial, visible, rfl⟩
      | mutable slot =>
          cases ht
          simp only [term, hl, bind, Option.bind_some]
          exact ⟨_, _, rfl, emit_typed trivial ⟨visible, rfl⟩⟩
  | @letE Γ R value u body t _ _ iv ib =>
      intro c locals resources supply rep
      obtain ⟨vf, s₁, hv, tv⟩ := iv c locals resources supply rep
      have rep₁ := rep.weaken (advance_extends c vf.instructions)
      obtain ⟨bf, s₂, hb, tb⟩ := ib _ _ _ s₁ (rep₁.withValue tv.2)
      simp only [term, hv, hb, bind, Option.bind_some]
      exact ⟨_, _, rfl, tb.prefix tv.1⟩
  | @letMut Γ R value u body t _ _ iv ib =>
      intro c locals resources supply rep
      obtain ⟨vf, s₁, hv, tv⟩ := iv c locals resources supply rep
      let slot : Mir.Slot := ⟨s₁.nextSlot, vf.value.ty⟩
      have rep₁ := rep.weaken (advance_extends c vf.instructions)
      have rep₂ : Represented ((advance c vf.instructions).withSlot slot)
          (.mutable slot :: locals) resources ((u, true) :: Γ) R := by
        simpa [slot, tv.2.2] using rep₁.withMutable slot
      obtain ⟨bf, s₂, hb, tb⟩ := ib _ _ _ { s₁ with nextSlot := s₁.nextSlot + 1 } rep₂
      simp only [term, hv, bind, Option.bind_some]
      change ∃ result next, (do
        let (body, s) ← term offset (.mutable slot :: locals) resources body
          { s₁ with nextSlot := s₁.nextSlot + 1 }
        pure (emit t (.mutableScope slot vf.value body.block) vf.instructions s)) = some (result, next) ∧ _
      rw [hb]
      exact ⟨_, _, rfl, emit_typed tv.1 ⟨⟨tv.2.1, rfl⟩, tb.block⟩⟩
  | @assign Γ index t R value hi _ iv =>
      intro c locals resources supply rep
      obtain ⟨l, hl, ht, visible⟩ := rep.local_lookup hi
      cases l with
      | value temp => cases ht
      | mutable slot =>
          have st : slot.ty = t := (Prod.mk.inj ht).1
          obtain ⟨vf, s₁, hv, tv⟩ := iv c locals resources supply rep
          simp only [term, hl, hv, bind, Option.bind_some]
          refine ⟨_, _, rfl, emit_typed tv.1 ?_⟩
          exact ⟨(advance_extends c vf.instructions).slots slot visible,
            ⟨tv.2.1, tv.2.2.trans st.symm⟩, rfl⟩
  | @whileE Γ R condition body _ _ ic ib =>
      intro c locals resources supply rep
      obtain ⟨cf, s₁, hc, tc⟩ := ic c locals resources supply rep
      obtain ⟨bf, s₂, hb, tb⟩ := ib c locals resources s₁ rep
      simp only [term, hc, hb, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed trivial ⟨tc.block, tb.block, rfl⟩⟩
  | @ifE Γ R condition yes t no _ _ _ ic iy ino =>
      intro c locals resources supply rep
      obtain ⟨cf, s₁, hc, tc⟩ := ic c locals resources supply rep
      have rep₁ := rep.weaken (advance_extends c cf.instructions)
      obtain ⟨yf, s₂, hy, ty⟩ := iy _ locals resources s₁ rep₁
      obtain ⟨nf, s₃, hn, tn⟩ := ino _ locals resources s₂ rep₁
      simp only [term, hc, hy, hn, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed tc.1 ⟨tc.2, ty.block, tn.block⟩⟩
  | @unary Γ R value op _ iv =>
      intro c locals resources supply rep
      obtain ⟨vf, s₁, hv, tv⟩ := iv c locals resources supply rep
      simp only [term, hv, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed tv.1 ⟨tv.2, rfl⟩⟩
  | @binary Γ R left u right v op t _ _ hop il ir =>
      intro c locals resources supply rep
      obtain ⟨lf, s₁, hl, tl⟩ := il c locals resources supply rep
      have rep₁ := rep.weaken (advance_extends c lf.instructions)
      obtain ⟨rf, s₂, hr, tr⟩ := ir _ locals resources s₁ rep₁
      by_cases logical : op = .and ∨ op = .or
      · obtain ⟨rfl, rfl, rfl⟩ := logical_types hop logical
        rcases logical with rfl | rfl
        · simp only [term, hl, hr, bind, Option.bind_some, true_or, ite_true]
          exact ⟨_, _, rfl, emit_typed tl.1 ⟨tl.2, tr.block, tl.2⟩⟩
        · simp only [term, hl, hr, bind, Option.bind_some, or_true, ite_true]
          exact ⟨_, _, rfl, emit_typed tl.1 ⟨tl.2, tl.2, tr.block⟩⟩
      · simp only [term, hl, hr, bind, Option.bind_some, ite_eq_right logical]
        refine ⟨_, _, rfl, emit_typed ((instructions_append_iff ..).mpr ⟨tl.1, tr.1⟩) ?_⟩
        rw [advance_append]
        exact ⟨(temp_weaken tl.2 (advance_extends _ _)).1, tr.2.1,
          fun h => logical (.inl h), fun h => logical (.inr h), by simpa [tl.2.2, tr.2.2] using hop⟩
  | @call function fn Γ R args hf hv _ ia =>
      intro c locals resources supply rep
      obtain ⟨af, s₁, ha, ta⟩ := ia c locals resources supply rep
      simp only [term, ha, bind, Option.bind_some]
      refine ⟨_, _, rfl, emit_typed ta.1 ?_⟩
      simp only [Mir.Operation.Typed, Mir.CallTyped, hf]
      exact ⟨hv, ta.2, trivial⟩
  | @tuple Γ R fields shape _ ia =>
      intro c locals resources supply rep
      obtain ⟨af, s₁, ha, ta⟩ := ia c locals resources supply rep
      simp only [term, ha, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed ta.1 ta.2⟩
  | @project Γ R value shape index t _ hi iv =>
      intro c locals resources supply rep
      obtain ⟨vf, s₁, hv, tv⟩ := iv c locals resources supply rep
      simp only [term, hv, bind, Option.bind_some]
      refine ⟨_, _, rfl, emit_typed tv.1 ?_⟩
      exact ⟨tv.2.1, by simp [tv.2.2, hi]⟩
  | @heap Γ R length initial success t failure site _ _ _ _ il ii iy ino =>
      intro c locals resources supply rep
      obtain ⟨lf, s₁, hl, tl⟩ := il c locals resources supply rep
      have rep₁ := rep.weaken (advance_extends c lf.instructions)
      obtain ⟨initial, s₂, hi, ti⟩ := ii _ locals resources s₁ rep₁
      obtain ⟨success, s₃, hy, ty⟩ := iy _ locals ((site + offset) :: resources) s₂ (rep₁.withOwner _)
      obtain ⟨failure, s₄, hn, tn⟩ := ino _ locals resources s₃ rep₁
      simp only [term, hl, hi, hy, hn, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed tl.1 ⟨tl.2, ti.block, ty.block, tn.block⟩⟩
  | @bufferLength R resource mode Γ hr =>
      intro c locals resources supply rep
      obtain ⟨rid, hi, hm⟩ := rep.resource_lookup hr
      simp only [term, hi, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed trivial ⟨⟨(rid, mode), hm, rfl⟩, rfl⟩⟩
  | @bufferRead R resource mode Γ index hr _ ii =>
      intro c locals resources supply rep
      obtain ⟨rid, hi, hm⟩ := rep.resource_lookup hr
      obtain ⟨vf, s₁, hv, tv⟩ := ii c locals resources supply rep
      simp only [term, hi, hv, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed tv.1
        ⟨⟨(rid, mode), (advance_extends c vf.instructions).resources _ hm, rfl⟩, tv.2, rfl⟩⟩
  | @bufferWrite R resource mode Γ index value hr hp _ _ ii iv =>
      intro c locals resources supply rep
      obtain ⟨rid, hi, hm⟩ := rep.resource_lookup hr
      obtain ⟨ix, s₁, hx, tx⟩ := ii c locals resources supply rep
      have rep₁ := rep.weaken (advance_extends c ix.instructions)
      obtain ⟨vf, s₂, hv, tv⟩ := iv _ locals resources s₁ rep₁
      simp only [term, hi, hx, hv, bind, Option.bind_some]
      exact ⟨_, _, rfl, emit_typed tx.1
        ⟨⟨(rid, mode), (advance_extends c ix.instructions).resources _ hm, rfl, hp⟩, tx.2, tv.block, rfl⟩⟩
  | @callView function fn mode R resource source Γ args hf hm hr hp _ ia =>
      intro c locals resources supply rep
      obtain ⟨rid, hi, binding⟩ := rep.resource_lookup hr
      obtain ⟨af, s₁, ha, ta⟩ := ia c locals resources supply rep
      simp only [term, hi, ha, bind, Option.bind_some]
      refine ⟨_, _, rfl, emit_typed ta.1 ?_⟩
      refine ⟨⟨(rid, source), (advance_extends c af.instructions).resources _ binding, rfl, hp⟩, ?_⟩
      simp only [Mir.CallTyped, hf]
      exact ⟨hm, ta.2, trivial⟩
  | @nil Γ R c locals resources supply rep =>
      exact ⟨_, _, rfl, trivial, by simp, rfl⟩
  | @cons Γ R value t values ts _ _ iv ia c locals resources supply rep =>
      obtain ⟨vf, s₁, hv, tv⟩ := iv c locals resources supply rep
      obtain ⟨af, s₂, ha, ta⟩ := ia _ locals resources s₁ (rep.weaken (advance_extends c vf.instructions))
      simp only [arguments, hv, ha, bind, Option.bind_some]
      exact ⟨_, _, rfl, arguments_cons_typed tv ta⟩

theorem parameters_types (types : List Ty) : (parameters types).map Mir.Temp.ty = types := by
  simp [parameters, List.map_map, Function.comp_def]

theorem parameters_length (types : List Ty) : (parameters types).length = types.length := by
  simpa using congrArg List.length (parameters_types types)

def initialContext (fn : Function) : Mir.Context :=
  ⟨parameters fn.params, [], match fn.view with | none => [] | some mode => [(0, mode.mode)]⟩

def initialResources (fn : Function) : List Nat := match fn.view with | none => [] | some _ => [0]

theorem initial_represented (fn : Function) :
    Represented (initialContext fn) ((parameters fn.params).reverse.map Local.value) (initialResources fn)
      fn.valueContext fn.resourceContext := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.valueContext, APL.FlatProducts.immutable, Local.spec, List.map_map,
      List.map_reverse, Function.comp_def] using
        congrArg (fun types => types.reverse.map (fun t => (t, false))) (parameters_types fn.params)
  · intro l hl
    obtain ⟨temp, ht, rfl⟩ := List.mem_map.mp hl
    exact List.mem_reverse.mp ht
  · unfold initialContext initialResources Function.resourceContext viewContext
    cases fn.view with
    | none => exact .nil
    | some mode => exact .cons (.head _) .nil

theorem function_typed_total {fn : Function}
    (h : HasType sigs fn.valueContext fn.resourceContext fn.body fn.result) :
    ∃ out, function fn = some out ∧ out.body.Typed sigs out.context out.result := by
  obtain ⟨body, supply, lowered, typed⟩ := term_typed (viewOffset fn.view) h
    (initialContext fn) _ (initialResources fn) ⟨(parameters fn.params).length, 0⟩ (initial_represented fn)
  refine ⟨⟨fn.id, fn.view.map (·, 0), parameters fn.params, fn.result, body.block,
    supply.nextTemp, supply.nextSlot, resourceCount (viewOffset fn.view) fn.body.heapSites⟩, ?_, ?_⟩
  · simp only [initialResources] at lowered
    unfold function
    dsimp only
    exact Option.bind_eq_some_iff.mpr ⟨(body, supply), lowered, rfl⟩
  · cases hv : fn.view <;> simpa [Mir.Function.context, initialContext, hv] using typed.block

theorem function_metadata {fn : Function} {out : Mir.Function} (h : function fn = some out) :
    out.id = fn.id ∧ out.signature = fn.signature ∧ out.view = fn.view.map (·, 0) ∧
      out.params = parameters fn.params ∧ out.result = fn.result := by
  simp only [function, bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨⟨body, supply⟩, _, eq⟩ := h
  cases eq
  simp [Mir.Function.signature, Function.signature, parameters_types, Option.map_map, Function.comp_def]

theorem function_typed {fn : Function} {out : Mir.Function}
    (h : HasType sigs fn.valueContext fn.resourceContext fn.body fn.result)
    (lowered : function fn = some out) : out.body.Typed sigs out.context out.result := by
  obtain ⟨candidate, hc, typed⟩ := function_typed_total h
  have eq : candidate = out := Option.some.inj (hc.symm.trans lowered)
  exact eq ▸ typed

private theorem function_list_total (functions : List Function)
    (h : ∀ fn ∈ functions, HasType sigs fn.valueContext fn.resourceContext fn.body fn.result) :
    ∃ result, functions.mapM function = some result := by
  induction functions with
  | nil => exact ⟨[], rfl⟩
  | cons fn rest ih =>
      obtain ⟨out, hf, _⟩ := function_typed_total (h fn (.head _))
      obtain ⟨outs, hr⟩ := ih (fun fn hfn => h fn (.tail _ hfn))
      exact ⟨out :: outs, by simp [List.mapM_cons, hf, hr]⟩

theorem program_total (h : WellFormedProgram p) : ∃ out, program p = some out := by
  obtain ⟨functions, hf⟩ := function_list_total p.functions.toList (fun fn hfn => (h.functions fn hfn).body)
  exact ⟨⟨"anl-memory-mir-v1", p.semanticRevision, p.profile, functions.toArray, p.entry⟩, by simp [program, hf]⟩

end ANL.Memory.Lowering
