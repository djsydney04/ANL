import ANL.WordsSafety
import ANL.MemoryLoans

namespace ANL.Words

open ANL.Memory

inductive Protected (ref : Ref) : List Frame → Prop where
  | here : loan.mode = .read → loan.source.ref = ref →
      Protected ref (.callReturn caller (some loan) :: k)
  | there : Protected ref k → Protected ref (frame :: k)

/-- Revocation ends the current loan before the separate caller restoration step. -/
def ReadLoanActive (ref : Ref) (s : State) : Prop :=
  match s.control with
  | .restore _ => Protected ref s.kont.tail
  | _ => Protected ref s.kont

theorem Protected.of_tail (h : Protected ref k.tail) : Protected ref k := by
  cases k with | nil => cases h | cons frame k => exact .there h

theorem ReadLoanActive.protected (h : ReadLoanActive ref s) : Protected ref s.kont := by
  unfold ReadLoanActive at h
  split at h
  · exact Protected.of_tail h
  · exact h

theorem Layout.protected (h : Layout owners resources k) (unique : (owners.map Shape.ref).Nodup)
    (hp : Protected ref k) :
    (∃ shape ∈ owners, shape.ref = ref) ∧
      (∀ binding ∈ resources, binding.mode.CanWrite → binding.ref ≠ ref) := by
  induction h generalizing ref with
  | nil => cases hp
  | plain plain _ ih =>
    cases hp with
    | here => cases plain
    | there hp => exact ih unique hp
  | @owner binding owners resources k site hm hl ih =>
    cases hp with
    | there hp =>
      have hu := List.nodup_cons.mp unique
      obtain ⟨⟨shape, hs, hr⟩, readOnly⟩ := ih hu.2 hp
      refine ⟨⟨shape, List.mem_cons_of_mem _ hs, hr⟩, ?_⟩
      intro other member writable
      rcases List.mem_cons.mp member with rfl | member
      · intro he
        exact hu.1 (List.mem_map.mpr ⟨shape, hs, hr.trans he.symm⟩)
      · exact readOnly other member writable
  | @callReturn loan owners k caller hv hl ih =>
    cases hp with
    | here hm hr =>
      obtain ⟨shape, hs, he, _⟩ := hl.live hv.1
      refine ⟨⟨shape, hs, he.trans hr⟩, ?_⟩
      intro binding hb writable
      simp only [loanResources, ANL.Memory.loanResources, List.mem_singleton] at hb
      subst binding
      simp [Loan.binding, hm, ViewMode.mode, Mode.CanWrite] at writable
    | there hp =>
      obtain ⟨live, readOnly⟩ := ih unique hp
      refine ⟨live, ?_⟩
      intro binding hb writable
      cases loan with
      | none => cases hb
      | some loan =>
        have eq : binding = loan.binding := by simpa only [loanResources, ANL.Memory.loanResources, List.mem_singleton] using hb
        subst binding
        exact readOnly loan.source hv.1 (Loan.write_source writable hv)

theorem State.Typed.protected_lookup (h : State.Typed p s t) (hp : ReadLoanActive ref s) :
    ∃ owner, s.world.lookup ref = some owner := by
  have hu : (s.world.owners.map Owner.shape |>.map Shape.ref).Nodup := by
    simpa [List.map_map, Function.comp_def, Owner.shape] using h.world.unique
  obtain ⟨⟨shape, hm, hr⟩, _⟩ := h.layout.protected hu hp.protected
  apply World.lookup_exists_of_mem
  have member := List.mem_map.mpr ⟨shape, hm, hr⟩
  simpa [List.map_map, Function.comp_def, Owner.shape] using member

theorem State.Typed.protected_readonly (h : State.Typed p s t) (hp : ReadLoanActive ref s)
    (hb : binding ∈ s.current.resources) (hw : binding.mode.CanWrite) : binding.ref ≠ ref := by
  have hu : (s.world.owners.map Owner.shape |>.map Shape.ref).Nodup := by
    simpa [List.map_map, Function.comp_def, Owner.shape] using h.world.unique
  exact (h.layout.protected hu hp.protected).2 binding hb hw

theorem resume_world : (resume result a k w).world = w := by cases result <;> rfl

theorem read_loan_step (h : State.Typed p s t) (hp : ReadLoanActive ref s)
    (hs : Step p responses s next) : next.world.lookup ref = s.world.lookup ref := by
  cases hs <;> try rfl
  all_goals try exact congrArg (fun w => w.lookup ref) resume_world
  case call => cases ‹List Term› <;> rfl
  case callView => cases ‹List Term› <;> rfl
  case argumentReturn => cases ‹List Term› <;> rfl
  case allocated ha =>
    obtain ⟨owner, hl⟩ := h.protected_lookup hp
    exact (allocate_eq_live_frame h.world hl ha).trans hl.symm
  case allocationRefused ha =>
    exact congrArg (fun owners => Store.lookup owners ref) (allocate_failure_owners ha (.inl rfl))
  case allocationRejected ha =>
    exact congrArg (fun owners => Store.lookup owners ref) (allocate_failure_owners ha (.inr rfl))
  case stored hs =>
    have original := h
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    cases hc with
    | store hm writable _ => exact World.write_other_ref hs (Ne.symm (original.protected_readonly hp hm writable))
  case closed hc =>
    obtain ⟨tail, rest, ho, hr, hm, hl⟩ := h.layout.owner_inv
    dsimp only at hr
    exact World.close_other hc (Ne.symm (h.protected_readonly hp (by simp [hr]) (.inl hm)))

/-- Every source transition remains within the loan interval; the last state may be its revocation. -/
inductive ReadLoanSteps (ref : Ref) (p : Program) (responses : Responses) : State → State → Prop where
  | refl : ReadLoanSteps ref p responses s s
  | head : ReadLoanActive ref s → Step p responses s middle →
      ReadLoanSteps ref p responses middle last → ReadLoanSteps ref p responses s last

theorem ReadLoanSteps.steps (h : ReadLoanSteps ref p responses s last) : Steps p responses s last := by
  induction h with
  | refl => exact .refl
  | head _ hs _ ih => exact .head hs ih

theorem read_loan_prefix (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hs : ReadLoanSteps ref p responses s last) : last.world.lookup ref = s.world.lookup ref := by
  induction hs with
  | refl => rfl
  | head hp hs _ ih => exact (ih (preservation wf h hs)).trans (read_loan_step h hp hs)

theorem grant_read_active (hm : loan.mode = .read) :
    ReadLoanActive loan.source.ref
      ⟨.eval body, ⟨f, values, loanResources (some loan)⟩, .callReturn caller (some loan) :: k, w⟩ :=
  .here hm rfl

theorem revoke_no_access :
    (State.mk (.restore value) a (.callReturn caller loan :: k) w).accessible = [] := rfl

theorem Layout.suspended_live (h : Layout owners resources k)
    (hf : Frame.callReturn caller loan ∈ k) (hb : binding ∈ caller.resources) :
    ∃ shape ∈ owners, shape.ref = binding.ref ∧ shape.length = binding.length := by
  induction h generalizing caller loan binding with
  | nil => cases hf
  | plain plain _ ih =>
    rcases List.mem_cons.mp hf with he | hf
    · subst he; cases plain
    · exact ih hf hb
  | owner _ _ ih =>
    rcases List.mem_cons.mp hf with he | hf
    · cases he
    · obtain ⟨shape, hm, hr, hn⟩ := ih hf hb
      exact ⟨shape, List.mem_cons_of_mem _ hm, hr, hn⟩
  | callReturn _ hl ih =>
    rcases List.mem_cons.mp hf with he | hf
    · cases he; exact hl.live hb
    · exact ih hf hb

theorem State.Typed.suspended_lookup (h : State.Typed p s t)
    (hf : Frame.callReturn caller loan ∈ s.kont) (hb : binding ∈ caller.resources) :
    ∃ owner, s.world.lookup binding.ref = some owner ∧ owner.length = binding.length := by
  obtain ⟨shape, hm, hr, hn⟩ := h.layout.suspended_live hf hb
  obtain ⟨owner, member, he⟩ := List.mem_map.mp hm
  subst shape
  change owner.ref = binding.ref at hr
  exact ⟨owner, by rw [← hr]; exact Store.lookup_of_mem h.world.unique member, hn⟩

theorem State.Typed.read_access (h : State.Typed p ⟨.readCell binding index, a, k, w⟩ t) :
    ∃ owner value, w.lookup binding.ref = some owner ∧ owner.length = binding.length ∧
      index < owner.length ∧ w.read binding.ref index = some value := by
  have original := h
  rcases h with ⟨hen, hc, hk, hl, hw⟩
  cases hc with
  | readCell hm hi =>
    obtain ⟨owner, ho, he⟩ := original.lookup hm
    obtain ⟨value, hv⟩ := World.read_exists ho (by simpa only [he] using hi)
    exact ⟨owner, value, ho, he, by simpa only [he] using hi, hv⟩

theorem State.Typed.write_access (h : State.Typed p ⟨.store binding index value, a, k, w⟩ t) :
    binding.mode.CanWrite ∧ ∃ owner next, w.lookup binding.ref = some owner ∧
      owner.length = binding.length ∧ index < owner.length ∧ w.write binding.ref index value = some next := by
  have original := h
  rcases h with ⟨hen, hc, hk, hl, hw⟩
  cases hc with
  | store hm hp hi =>
    obtain ⟨owner, ho, he⟩ := original.lookup hm
    obtain ⟨next, hs⟩ := World.write_exists (value := value) ho (by simpa only [he] using hi)
    exact ⟨hp, owner, next, ho, he, by simpa only [he] using hi, hs⟩

end ANL.Words
