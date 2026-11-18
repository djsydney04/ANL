import ANL.BootCheck
import ANL.BootPolicyProofs

namespace ANL.Boot

open ANL.Words

variable {p : Program} {f g : Nat} {d : Defined} {op : Operation}

theorem checkProgram_iff : checkProgram p = true ↔ WellFormedProgram p := by
  simp only [checkProgram, Bool.and_eq_true, decide_eq_true_eq, checkMetadata_iff,
    checkOrdered_iff, List.all_eq_true, checkDeclaration_iff, checkRoles_iff,
    checkDiscovery_iff, checkGraph_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hm, ho⟩, hi⟩, hn⟩, hd⟩, hr⟩, hdisc⟩, hg⟩
    exact ⟨hm, ho, hi, hn, hd, hr, hdisc, hg⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨h.metadata, h.ordered⟩, h.ids⟩, h.names⟩, h.declarations⟩, h.roles⟩, h.discovery⟩, h.acyclic⟩

theorem WellFormedProgram.at {decl : Declaration} (h : WellFormedProgram p)
    (found : p.functions[f]? = some decl) : DeclarationValid p decl :=
  h.declarations decl (List.mem_of_getElem? found)

theorem WellFormedProgram.id_at {decl : Declaration} (h : WellFormedProgram p)
    (found : p.functions[f]? = some decl) : decl.id = f := by
  have bound := List.getElem?_eq_some_iff.mp found |>.1
  have ids := congrArg (fun ids => ids[f]?) h.ids
  simpa [List.getElem?_map, found, List.getElem?_range bound] using ids

theorem BootPrefix.memoryFree (h : BootPrefix p body rest) (restFree : MemoryFree rest) :
    MemoryFree body := by
  cases h
  simpa [MemoryFree] using restFree

theorem FunctionPolicy.memoryFree (h : FunctionPolicy p d) : MemoryFree d.function.body := by
  unfold FunctionPolicy at h
  split at h
  · obtain ⟨rest, pre, policy⟩ := h
    exact pre.memoryFree policy.1
  · exact h.1

theorem WellFormedProgram.memoryFree (h : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) : MemoryFree d.function.body :=
  (h.at found).policy.memoryFree

theorem WellFormedProgram.no_view (h : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) : d.function.view = none :=
  (h.at found).view

theorem TargetAllowed.bound (h : TargetAllowed p effects f) : f < p.functions.length := by
  rcases h with ⟨_, h⟩
  cases found : p.functions[f]? with
  | none => simp [found] at h
  | some d => exact List.getElem?_eq_some_iff.mp found |>.1

theorem TargetAllowed.not_role (h : TargetAllowed p effects f) : f ∉ p.roleIDs := h.1

theorem RolesValid.role_defined (roles : RolesValid p) (role : f ∈ p.roleIDs) :
    ∃ d, p.functions[f]? = some (.defined d) := by
  simp only [Program.roleIDs, List.mem_cons, List.not_mem_nil, or_false] at role
  rcases role with rfl | rfl | rfl
  · cases roles.boot with | intro found _ _ _ => exact ⟨_, found⟩
  · cases roles.hardware with | intro found _ _ _ => exact ⟨_, found⟩
  · cases roles.language with | intro found _ _ _ => exact ⟨_, found⟩

theorem operationAt_found (found : p.operationAt f = some op) :
    ∃ d, p.functions[f]? = some (.primitive d) ∧ d.operation = op := by
  unfold Program.operationAt at found
  split at found
  next d lookup => cases found; exact ⟨d, lookup, rfl⟩
  next => contradiction

theorem operationAt_validTarget (roles : RolesValid p) (found : p.operationAt f = some op) :
    f < p.functions.length ∧ f ∉ p.roleIDs := by
  obtain ⟨d, lookup, _⟩ := operationAt_found found
  refine ⟨List.getElem?_eq_some_iff.mp lookup |>.1, ?_⟩
  intro role
  obtain ⟨fn, defLookup⟩ := roles.role_defined role
  rw [lookup] at defLookup
  cases defLookup

theorem BodyPolicy.call_target (h : BodyPolicy p effects body) (mem : f ∈ calls body) :
    f < p.functions.length ∧ f ∉ p.roleIDs :=
  ⟨(h.2 f mem).bound, (h.2 f mem).not_role⟩

theorem BootPrefix.call_target (roles : RolesValid p) (pre : BootPrefix p body rest)
    (policy : BodyPolicy p effects rest) (mem : f ∈ calls body) :
    f < p.functions.length ∧ f ∉ p.roleIDs := by
  cases pre with
  | intro hc hd hi =>
    simp [calls] at mem
    rcases mem with rfl | rfl | rfl | mem
    · exact operationAt_validTarget roles hc
    · exact operationAt_validTarget roles hd
    · exact operationAt_validTarget roles hi
    · exact policy.call_target mem

theorem FunctionPolicy.call_target (roles : RolesValid p) (h : FunctionPolicy p d)
    (mem : f ∈ calls d.function.body) : f < p.functions.length ∧ f ∉ p.roleIDs := by
  unfold FunctionPolicy at h
  split at h
  · obtain ⟨rest, pre, policy⟩ := h
    exact pre.call_target roles policy mem
  · exact h.call_target mem

theorem WellFormedProgram.call_target (h : WellFormedProgram p)
    (found : p.functions[g]? = some (.defined d)) (mem : f ∈ calls d.function.body) :
    f < p.functions.length ∧ f ∉ p.roleIDs :=
  (h.at found).policy.call_target h.roles mem

theorem WellFormedProgram.no_synthetic_call (h : WellFormedProgram p)
    (found : p.functions[g]? = some (.defined d)) : p.functions.length ∉ calls d.function.body := by
  intro mem
  have := h.call_target found mem |>.1
  omega

theorem BodyPolicy.no_machine (h : BodyPolicy p effects body) (mem : f ∈ calls body)
    (found : p.operationAt f = some op) : op.effects ≠ [0] := by
  obtain ⟨d, lookup, rfl⟩ := operationAt_found found
  have allow := h.2 f mem |>.2
  simp only [lookup] at allow
  rw [allow.1]
  decide

theorem WellFormedProgram.no_cycles (h : WellFormedProgram p) : CycleFree p := h.acyclic.no_cycle

theorem WellFormedProgram.boot_nonreturning (h : WellFormedProgram p)
    (found : p.functions[p.entries.boot.function]? = some (.defined d)) :
    NoNormalReturn p.signatures d.function.valueContext [] d.function.body d.function.result :=
  ⟨(h.at found).typed, h.roles.bootTail d found⟩

theorem WellFormedProgram.handler_nonreturning (h : WellFormedProgram p)
    (role : f = p.entries.hardware.function ∨ f = p.entries.language.function)
    (found : p.functions[f]? = some (.defined d)) :
    NoNormalReturn p.signatures d.function.valueContext [] d.function.body d.function.result := by
  refine ⟨(h.at found).typed, ?_⟩
  have body : d.function.body = handler := by
    rcases role with rfl | rfl
    · exact h.roles.hardwareBody d found
    · exact h.roles.languageBody d found
  rw [body]
  exact handler_selected.hasTail

theorem FirstUses.mem_iff (h : FirstUses uses keys) : op ∈ keys ↔ op ∈ uses := by
  induction h with
  | nil => simp
  | cons _ ih =>
    simp only [List.mem_cons, ih, List.mem_filter, decide_eq_true_eq]
    grind

theorem FirstUses.nodup (h : FirstUses uses keys) : keys.Nodup := by
  induction h with
  | nil => exact .nil
  | cons prev ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro mem
    have bad := prev.mem_iff.mp mem
    simp at bad

theorem WellFormedProgram.primitive_keys_unique (h : WellFormedProgram p) :
    (p.primitives.map Primitive.operation).Nodup := h.discovery.nodup

theorem WellFormedProgram.no_unused_primitive {primitive : Primitive} (h : WellFormedProgram p)
    (mem : primitive ∈ p.primitives) : primitive.operation ∈ p.operationUses :=
  h.discovery.mem_iff.mp (List.mem_map.mpr ⟨primitive, mem, rfl⟩)

end ANL.Boot
