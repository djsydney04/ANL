import ANL.BootV3Check
import ANL.BootV2CheckProofs

namespace ANL.Boot.V3

open ANL.Words

variable {p : Program} {d : Defined}

theorem checkMetadata_iff : checkMetadata p = true ↔ MetadataValid p := by
  simp only [checkMetadata, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hr, ho, hp, hi, hst, hd, hrs, hrd⟩
    exact ⟨hs, hr, ho, hp, hi, hst, hd, hrs, hrd⟩
  · intro h
    exact ⟨h.schema, h.revision, h.ordinary, h.profile, h.image, h.stacks, h.devices,
      h.roleStacks, h.roleDistinct⟩

theorem checkDefined_iff : checkDefined p d = true ↔ DefinedValid p d := by
  simp only [checkDefined, Bool.and_eq_true, decide_eq_true_eq, checkTerm_iff,
    V2.checkFunctionPolicy_iff]
  constructor
  · rintro ⟨⟨⟨hn, hv, he⟩, ht⟩, hp⟩
    exact ⟨hn, hv, he, ht, hp⟩
  · intro h
    exact ⟨⟨⟨h.name, h.view, h.effects⟩, h.typed⟩, h.policy⟩

theorem checkDeclaration_iff {decl : Declaration} :
    checkDeclaration p decl = true ↔ DeclarationValid p decl := by
  cases decl <;> simp only [checkDeclaration, DeclarationValid, checkDefined_iff,
    V2.checkPrimitive_iff]

theorem checkRoles_iff : checkRoles p = true ↔ RolesValid p := by
  simp only [checkRoles, Bool.and_eq_true, V2.checkRole_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨boot, hardware⟩, language⟩, bt⟩, ht⟩, lb⟩
    exact ⟨boot, hardware, language,
      (V2.roleBodyCheck_iff boot (fun _ => designatedTail_isSome_iff)).mp bt,
      (V2.roleBodyCheck_iff hardware (fun _ => designatedTail_isSome_iff)).mp ht,
      (V2.roleBodyCheck_iff language (fun _ => isHandler_iff)).mp lb⟩
  · intro h
    exact ⟨⟨⟨⟨⟨h.boot, h.hardware⟩, h.language⟩,
      (V2.roleBodyCheck_iff h.boot (fun _ => designatedTail_isSome_iff)).mpr h.bootTail⟩,
      (V2.roleBodyCheck_iff h.hardware (fun _ => designatedTail_isSome_iff)).mpr h.hardwareTail⟩,
      (V2.roleBodyCheck_iff h.language (fun _ => isHandler_iff)).mpr h.languageBody⟩

theorem checkProgram_iff : checkProgram p = true ↔ WellFormedProgram p := by
  simp only [checkProgram, Bool.and_eq_true, decide_eq_true_eq, checkMetadata_iff,
    V2.checkOrdered_iff, List.all_eq_true, checkDeclaration_iff, checkRoles_iff,
    V2.checkDiscovery_iff, V2.checkGraph_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hm, ho⟩, hi⟩, hn⟩, hd⟩, hr⟩, hdisc⟩, hg⟩
    exact ⟨hm, ho, hi, hn, hd, hr, hdisc, hg⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨h.metadata, h.ordered⟩, h.ids⟩, h.names⟩, h.declarations⟩,
      h.roles⟩, h.discovery⟩, h.acyclic⟩

theorem WellFormedProgram.at {decl : Declaration} {f : Nat}
    (h : WellFormedProgram p) (found : p.functions[f]? = some decl) :
    DeclarationValid p decl :=
  h.declarations decl (List.mem_of_getElem? found)

theorem WellFormedProgram.memoryFree {f : Nat} (h : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) : MemoryFree d.function.body :=
  V2.FunctionPolicy.memoryFree (h.at found).policy

theorem MetadataValid.excludes_older_schema (h : MetadataValid p) :
    p.schema ≠ "anl-boot-core-v1" ∧ p.schema ≠ "anl-boot-core-v2" := by
  rw [h.schema]
  decide

theorem WellFormedProgram.not_v2 (h : WellFormedProgram p) :
    ¬ V2.WellFormedProgram p := by
  intro old
  exact h.metadata.excludes_older_schema.2 old.metadata.schema

theorem checked_not_v2 (checked : checkProgram p = true) :
    V2.checkProgram p = false := by
  cases old : V2.checkProgram p with
  | false => rfl
  | true => exact False.elim ((checkProgram_iff.mp checked).not_v2 (V2.checkProgram_iff.mp old))

end ANL.Boot.V3
