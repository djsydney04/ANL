import ANL.BootPolicy
import ANL.BootTail

namespace ANL.Boot

open ANL.Words

theorem checkOperation_iff : checkOperation hardware op = true ↔ op.Valid hardware := by
  cases op with
  | read8 region offset =>
    simp only [checkOperation, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact .read8
    · intro h; cases h; exact ⟨rfl, rfl⟩
  | write8 region offset =>
    simp only [checkOperation, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, h⟩; exact .write8 h
    · intro h; cases h with | write8 h => exact ⟨rfl, h⟩
  | fence region =>
    simp only [checkOperation, decide_eq_true_eq]
    constructor
    · rintro rfl; exact .fence
    · intro h; cases h; rfl
  | csrClear authority register mask =>
    simp only [checkOperation, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact .csrClear
    · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  | csrWrite authority register value =>
    simp only [checkOperation, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact .csrWrite
    · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  | installTrap authority handler =>
    simp only [checkOperation, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact .installTrap
    · intro h; cases h; exact ⟨rfl, rfl⟩

theorem checkMetadata_iff : checkMetadata p = true ↔ MetadataValid p := by
  simp only [checkMetadata, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hr, ho, hp, hi, hst, hd, hrs, hrd⟩
    exact ⟨hs, hr, ho, hp, hi, hst, hd, hrs, hrd⟩
  · intro h
    exact ⟨h.schema, h.revision, h.ordinary, h.profile, h.image, h.stacks, h.devices, h.roleStacks, h.roleDistinct⟩

theorem checkOrdered_iff : checkOrdered phase declarations = true ↔ Ordered phase declarations := by
  induction declarations generalizing phase with
  | nil => simp only [checkOrdered, true_iff]; exact .nil
  | cons d rest ih =>
    cases d with
    | defined d =>
      cases phase with
      | false =>
        simp only [checkOrdered, ih]
        exact ⟨Ordered.defined, fun h => by cases h; assumption⟩
      | true =>
        simp only [checkOrdered, Bool.false_eq_true, false_iff]
        intro h; cases h
    | primitive d =>
      simp only [checkOrdered, ih]
      exact ⟨Ordered.primitive, fun h => by cases h; assumption⟩

theorem checkPrimitive_iff : checkPrimitive p d = true ↔ PrimitiveValid p d := by
  simp only [checkPrimitive, Bool.and_eq_true, decide_eq_true_eq, checkOperation_iff]
  constructor
  · rintro ⟨⟨hn, hi, hp, hr, he⟩, ho⟩; exact ⟨hn, hi, ho, hp, hr, he⟩
  · intro h; exact ⟨⟨h.name, h.identifier, h.params, h.result, h.effects⟩, h.operation⟩

theorem checkBodyPolicy_iff : checkBodyPolicy p effects body = true ↔ BodyPolicy p effects body := by
  simp [checkBodyPolicy, BodyPolicy, checkMemoryFree_iff, List.all_eq_true]

theorem bootRest_iff : bootRest p body = some rest ↔ BootPrefix p body rest := by
  constructor
  · intro h
    unfold bootRest at h
    split at h
    next t₁ a₁ clear t₂ a₂ disable t₃ a₃ install remaining =>
      split at h
      next valid =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hc, hd, hi⟩ := valid
        cases h
        exact .intro hc hd hi
      next => contradiction
    next => contradiction
  · intro h
    cases h with
    | intro hc hd hi => simp [bootRest, hc, hd, hi]

theorem checkFunctionPolicy_iff : checkFunctionPolicy p d = true ↔ FunctionPolicy p d := by
  unfold checkFunctionPolicy FunctionPolicy
  split
  · cases eq : bootRest p d.function.body with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨rest, pre, _⟩
      have := bootRest_iff.mpr pre
      simp [eq] at this
    | some rest =>
      rw [checkBodyPolicy_iff]
      constructor
      · intro h; exact ⟨rest, bootRest_iff.mp eq, h⟩
      · rintro ⟨other, pre, policy⟩
        have same := eq.symm.trans (bootRest_iff.mpr pre)
        cases same
        exact policy
  · exact checkBodyPolicy_iff

theorem checkDefined_iff : checkDefined p d = true ↔ DefinedValid p d := by
  simp only [checkDefined, Bool.and_eq_true, decide_eq_true_eq, checkTerm_iff, checkFunctionPolicy_iff]
  constructor
  · rintro ⟨⟨⟨hn, hv, he⟩, ht⟩, hp⟩; exact ⟨hn, hv, he, ht, hp⟩
  · intro h; exact ⟨⟨⟨h.name, h.view, h.effects⟩, h.typed⟩, h.policy⟩

theorem checkDeclaration_iff : checkDeclaration p d = true ↔ DeclarationValid p d := by
  cases d <;> simp only [checkDeclaration, DeclarationValid, checkDefined_iff, checkPrimitive_iff]

theorem checkRole_iff : checkRole p f params = true ↔ RoleValid p f params := by
  constructor
  · intro h
    unfold checkRole at h
    split at h
    next d found =>
      simp only [decide_eq_true_eq] at h
      exact .intro found h.1 h.2.1 h.2.2
    next => contradiction
  · intro h
    cases h with
    | intro found view params result => simp [checkRole, found, view, params, result]

theorem roleBodyCheck_iff {check : Term → Bool} {predicate : Term → Prop} (role : RoleValid p f params)
    (correct : ∀ body, check body = true ↔ predicate body) :
    roleBodyCheck p f check = true ↔
      ∀ d, p.functions[f]? = some (.defined d) → predicate d.function.body := by
  cases role with
  | intro found _ _ _ => simp [roleBodyCheck, found, correct]

theorem checkRoles_iff : checkRoles p = true ↔ RolesValid p := by
  simp only [checkRoles, Bool.and_eq_true, checkRole_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨boot, hardware⟩, language⟩, tail⟩, hb⟩, lb⟩
    exact ⟨boot, hardware, language,
      (roleBodyCheck_iff boot (fun _ => designatedTail_isSome_iff)).mp tail,
      (roleBodyCheck_iff hardware (fun _ => isHandler_iff)).mp hb,
      (roleBodyCheck_iff language (fun _ => isHandler_iff)).mp lb⟩
  · intro h
    exact ⟨⟨⟨⟨⟨h.boot, h.hardware⟩, h.language⟩,
      (roleBodyCheck_iff h.boot (fun _ => designatedTail_isSome_iff)).mpr h.bootTail⟩,
      (roleBodyCheck_iff h.hardware (fun _ => isHandler_iff)).mpr h.hardwareBody⟩,
      (roleBodyCheck_iff h.language (fun _ => isHandler_iff)).mpr h.languageBody⟩

theorem firstUses_cons : firstUses (first :: rest) =
    first :: firstUses (rest.filter (fun op => decide (op ≠ first))) := by
  simp [firstUses, List.eraseDupsBy_cons]

theorem firstUses_sound (uses : List Operation) : FirstUses uses (firstUses uses) := by
  match uses with
  | [] => exact .nil
  | first :: rest =>
    rw [firstUses_cons]
    exact .cons (firstUses_sound _)
termination_by uses.length
decreasing_by have := List.length_filter_le (fun op => decide (op ≠ first)) rest; simp_all; omega

theorem FirstUses.complete (h : FirstUses uses keys) : firstUses uses = keys := by
  induction h with
  | nil => rfl
  | cons _ ih => rw [firstUses_cons, ih]

theorem firstUses_iff : firstUses uses = keys ↔ FirstUses uses keys := by
  constructor
  · rintro rfl; exact firstUses_sound uses
  · exact FirstUses.complete

theorem checkDiscovery_iff : checkDiscovery p = true ↔ DiscoveryValid p := by
  simp [checkDiscovery, DiscoveryValid, firstUses_iff]

end ANL.Boot
