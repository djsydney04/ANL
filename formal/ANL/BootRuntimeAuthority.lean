import ANL.BootRuntimeSafety

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program}

 theorem let_call_occurrence (occurrence : Origin.At (.letE t a b) path (.call u ident args)) :
    (∃ rest, path = .letValue :: rest ∧ Origin.At a rest (.call u ident args)) ∨
    (∃ rest, path = .letBody :: rest ∧ Origin.At b rest (.call u ident args)) := by
  cases occurrence with | child child tail =>
   cases child
   · exact .inl ⟨_, rfl, tail⟩
   · exact .inr ⟨_, rfl, tail⟩

 theorem empty_call_occurrence (occurrence : Origin.At (.call t target []) path (.call u ident args)) :
    path = [] ∧ target = ident ∧ args = [] := by
  cases occurrence with
  | root => exact ⟨rfl, rfl, rfl⟩
  | child child _ => cases child with | argument found => simp at found

/-- The machine-authority exceptions name exact authored occurrences, not arbitrary calls to a signature. -/
inductive PrefixAuthority (p : Program) : Origin.Location → Nat → Prop where
  | clear : p.operationAt ident = some (.csrClear 0 "sstatus" 2) →
      PrefixAuthority p ⟨p.entries.boot.function, [.letValue]⟩ ident
  | disable : p.operationAt ident = some (.csrWrite 0 "sie" 0) →
      PrefixAuthority p ⟨p.entries.boot.function, [.letBody, .letValue]⟩ ident
  | install : p.operationAt ident = some (.installTrap 0 p.entries.hardware.function) →
      PrefixAuthority p ⟨p.entries.boot.function, [.letBody, .letBody, .letValue]⟩ ident

 theorem prefix_call_authority (prefixPolicy : BootPrefix p body rest)
    (occurrence : Origin.At body path (.call ty ident args)) :
    PrefixAuthority p ⟨p.entries.boot.function, path⟩ ident ∨
      ∃ suffix, path = .letBody :: .letBody :: .letBody :: suffix ∧ Origin.At rest suffix (.call ty ident args) := by
  cases prefixPolicy with | intro clear disable install =>
   rcases let_call_occurrence occurrence with ⟨sub1, rfl, child1⟩ | ⟨sub1, rfl, child1⟩
   · rcases empty_call_occurrence child1 with ⟨rfl, rfl, _⟩
     exact .inl (.clear clear)
   · rcases let_call_occurrence child1 with ⟨sub2, rfl, child2⟩ | ⟨sub2, rfl, child2⟩
     · rcases empty_call_occurrence child2 with ⟨rfl, rfl, _⟩
       exact .inl (.disable disable)
     · rcases let_call_occurrence child2 with ⟨sub3, rfl, child3⟩ | ⟨sub3, rfl, child3⟩
       · rcases empty_call_occurrence child3 with ⟨rfl, rfl, _⟩
         exact .inl (.install install)
       · exact .inr ⟨sub3, rfl, child3⟩

inductive SourceAuthority (p : Program) (origin : Origin.Location) (target : Nat) : Prop where
  | machine : PrefixAuthority p origin target → SourceAuthority p origin target
  | body : p.functions[origin.function]? = some (.defined definition) →
      TargetAllowed p definition.effects target → SourceAuthority p origin target

 theorem located_call_authority (wf : WellFormedProgram p) (located : Origin.Located p origin (.call ty target args)) :
    SourceAuthority p origin target := by
  obtain ⟨definition, found⟩ := located.function_defined
  have occurrence : Origin.At definition.function.body origin.path (.call ty target args) := by
    apply Origin.lookupTerm_iff.mp
    have raw := Origin.lookup_iff.mpr located
    simpa [Origin.lookup, found] using raw
  have policy := (wf.at found).policy
  have identifier := wf.id_at found
  change definition.function.id = origin.function at identifier
  by_cases boot : origin.function = p.entries.boot.function
  · simp only [FunctionPolicy, identifier, boot, ↓reduceIte] at policy
    obtain ⟨rest, prefixPolicy, bodyPolicy⟩ := policy
    rcases prefix_call_authority prefixPolicy occurrence with machine | ⟨suffix, _, remaining⟩
    · exact .machine (by
        cases origin with | mk function path =>
         simp only at boot
         subst function
         exact machine)
    · exact .body found (bodyPolicy.2 _ (remaining.calls (by simp [calls])))
  · simp only [FunctionPolicy, identifier, boot, ↓reduceIte] at policy
    exact .body found (policy.2 _ (occurrence.calls (by simp [calls])))

 theorem PendingAt.located (pending : PendingAt p s q) :
    ∃ ty args, Origin.Located p q.origin (.call ty q.declaration args) := by
  rcases pending with ⟨_, _, _, _, _, facts⟩
  split at facts
  next ident values row ty target terms controlEq found located =>
    rcases facts with ⟨_, rfl, _, _, _, _⟩
    exact ⟨ty, terms, Origin.lookup_iff.mp located⟩
  next => contradiction

 theorem PendingAt.authority (wf : WellFormedProgram p) (pending : PendingAt p s q) :
    SourceAuthority p q.origin q.declaration := by
  obtain ⟨ty, args, located⟩ := pending.located
  exact located_call_authority wf located

 theorem SourceAuthority.operation_boundary (wf : WellFormedProgram p)
    (authority : SourceAuthority p origin ident) (found : p.functions[ident]? = some (.primitive row)) :
    PrefixAuthority p origin ident ∨
      ∃ definition, p.functions[origin.function]? = some (.defined definition) ∧
        1 ∈ definition.effects ∧ row.operation.effects = [1] := by
  cases authority with
  | machine prefixPolicy => exact .inl prefixPolicy
  | body definitionFound permitted =>
    have policy := primitive_valid wf found
    simp only [TargetAllowed, found] at permitted
    have device := permitted.2.1
    have allowed := permitted.2.2 1 (by rw [policy.effects, device]; simp)
    exact .inr ⟨_, definitionFound, allowed, device⟩

 theorem PendingAt.machine_authority (wf : WellFormedProgram p) (pending : PendingAt p s q)
    (machine : q.operation.effects ≠ [1]) : PrefixAuthority p q.origin q.declaration := by
  obtain ⟨values, row, _, found, operation, _⟩ := pending.invocation
  rcases (pending.authority wf).operation_boundary wf found with prefixPolicy | ⟨_, _, _, device⟩
  · exact prefixPolicy
  · rw [operation] at device
    exact False.elim (machine device)

end ANL.Boot.Runtime
