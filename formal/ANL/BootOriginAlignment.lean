import ANL.BootOriginAdvanceProofs
import ANL.WordsSafety

namespace ANL.Boot.Origin
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem Pending.first : Pending (e :: es) es 0 := ⟨[], e, rfl, rfl⟩

 theorem Pending.next (h : Pending all (e :: es) n) : Pending all es (n + 1) := by
  obtain ⟨before, current, rfl, rfl⟩ := h
  exact ⟨before ++ [current], e, by simp, by simp⟩

 theorem Pending.lookup_next (h : Pending all (e :: es) n) : all[n + 1]? = some e := by
  obtain ⟨before, current, rfl, rfl⟩ := h
  simp

 theorem Pending.done (h : Pending all [] n) : n + 1 = all.length := by
  obtain ⟨before, current, rfl, rfl⟩ := h
  simp

 theorem carrier_defined {p : ANL.Boot.Program} {d : Defined} {f : Nat} (h : p.functions[f]? = some (Declaration.defined d)) :
    p.carrier.functions[f]? = some d.function := by
  have bound := List.getElem?_eq_some_iff.mp h
  simp only [Program.carrier]
  rw [Array.getElem?_push_lt (by simpa using bound.1)]
  simp [h, List.getElem?_map, bound.choose_spec, Declaration.carrierFunction]

 theorem DefinedTarget.found (h : DefinedTarget p f) : ∃ d, p.functions[f]? = some (.defined d) := by
  unfold DefinedTarget at h
  split at h <;> simp_all

 theorem Aligned.resume (located : Located p o e) (hf : o.function = a.function)
    (frames : StackAt p a.function origins k) :
    Aligned p (resume result a k w) ⟨o, origins⟩ := by
  cases result with
  | value => exact ⟨hf, .ret located, frames⟩
  | trap => exact ⟨hf, .trap located, frames⟩
  | invalid => exact ⟨hf, .invalid located, frames⟩

 theorem preserve (wf : WellFormedProgram p) (typed : State.Typed p.carrier s t)
    (aligned : Aligned p s metadata) (transition : Step p responses s metadata next result) :
    Aligned p next result := by
  obtain ⟨allowed, actual, choice, move⟩ := transition
  have safe := ANL.Words.preservation (carrier_wellFormed wf) typed actual
  have valid := safe.not_invalid
  have movement := advance_iff.mpr ⟨_, choice, move⟩
  clear choice move safe typed
  cases metadata with | mk origin origins =>
   obtain ⟨hf, hc, hk⟩ := aligned
   cases actual
   all_goals try simp [Admitted] at allowed
   all_goals try exact False.elim (valid rfl)
   all_goals simp only at hf hc hk
   case lit =>
     cases hc
     simp [advance, action, applyAction] at movement
     cases movement
     exact ⟨hf, .ret (by assumption), hk⟩
   all_goals try cases hc
   all_goals try simp [advance, action, applyAction] at movement
   all_goals try cases movement
   all_goals try exact ⟨hf, .ret (by assumption), hk⟩
   all_goals try (apply Aligned.resume <;> assumption)
   all_goals try
     refine ⟨hf, .eval (Located.child (by assumption) (by constructor <;> rfl)), ?_⟩
     rw [← hf] at hk ⊢
     exact .cons (by constructor <;> first | assumption | exact Pending.first) hk
   case call.eval =>
     rename_i ty f args a k w occurrence
     cases args with
     | nil =>
       simp at movement
       cases movement
       exact ⟨hf, .invoke occurrence rfl, hk⟩
     | cons e es =>
       simp at movement
       cases movement
       refine ⟨hf, .eval (occurrence.child (.argument rfl)), ?_⟩
       change StackAt p a.function _ _
       rw [← hf] at hk ⊢
       exact .cons (.arguments occurrence Pending.first) hk
   case invoke.invoke.refl =>
     exact ⟨hf, .grant (by assumption) (by assumption) allowed, hk⟩
   case grant.grant.refl =>
     rename_i f fn values a k w found ty args occurrence target arity
     obtain ⟨d, hd⟩ := target.found
     have eq : fn = d.function := Option.some.inj (found.symm.trans (carrier_defined hd))
     subst fn
     exact ⟨rfl, .eval (.root hd), .cons (.caller occurrence hf.symm target) hk⟩
   all_goals try exact ⟨hf, .revoke (by assumption), hk⟩
   all_goals try exact ⟨hf, .restore (by assumption), hk⟩
   all_goals cases origin
   all_goals simp only at hf hk
   all_goals rw [← hf] at hk
   all_goals cases hk with | cons head tail =>
     cases head
     all_goals try simp_all only [Bool.false_eq_true, Bool.not_eq_true, ite_true, ite_false]
     all_goals try simp at movement
     all_goals try cases movement
     all_goals try rw [hf] at tail
     all_goals try exact ⟨hf, .ret (by assumption), tail⟩
     all_goals try (apply Aligned.resume <;> assumption)
     all_goals try exact ⟨hf, .eval (Located.child (by assumption) (by constructor)), tail⟩
     all_goals try
       refine ⟨hf, .eval (Located.child (by assumption) (by constructor <;> exact Pending.lookup_next (by assumption))), ?_⟩
       simp only
       rw [← hf] at tail ⊢
       exact .cons (by first
         | exact FrameAt.scope (by assumption)
         | exact FrameAt.scopeMut (by assumption)
         | (constructor <;> first | assumption | exact Pending.next (by assumption))) tail
     all_goals first
     | (case arguments =>
         rename_i v a f rest values k w e path parent parents ty args current occurrence pending
         cases rest with
         | nil =>
           simp at movement
           cases movement
           exact ⟨hf, .invoke occurrence (Pending.done pending), tail⟩
         | cons arg rest =>
           simp at movement
           cases movement
           refine ⟨hf, .eval (occurrence.child (.argument pending.lookup_next)), ?_⟩
           change StackAt p a.function _ _
           rw [← hf] at tail ⊢
           exact .cons (.arguments occurrence pending.next) tail
             )
     | (case caller.refl =>
         rename_i agreement
         exact ⟨agreement.symm, .ret (by assumption), agreement ▸ tail⟩)

end ANL.Boot.Origin
