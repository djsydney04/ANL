import APL.ProductFlowSupport

namespace APL.ProductEntry

open ProductLogic ProductFlow
open VCG (MVal Model)

def runtimeLeaves : FlatProducts.Val → List APL.Val
  | .scalar value => [value]
  | .tuple fields => fields.fields

def parameterModel (values : List FlatProducts.Val) : Model :=
  fun slot => VCG.embed (((values.flatMap runtimeLeaves)[slot]?).getD .unit)

theorem runtime_leaves_width (value : FlatProducts.Val) :
    (runtimeLeaves value).length = leafWidth value.type := by
  cases value <;> simp [runtimeLeaves, leafWidth, leafTypes, FlatProducts.Val.type, FlatProducts.Flat.map]

theorem runtime_leaves_count (values : List FlatProducts.Val) :
    (values.flatMap runtimeLeaves).length = reservedCount (values.map FlatProducts.Val.type) := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [reservedCount, runtime_leaves_width, ih]

theorem parameter_model_leaf (h : (values.flatMap runtimeLeaves)[slot]? = some value) :
    parameterModel values slot = VCG.embed value := by
  simp [parameterModel, h]

private theorem parameter_fields_denote (values : List APL.Val) (offset : Nat)
    (hm : ∀ index value, values[index]? = some value → model (offset + index) = VCG.embed value) :
    FieldsDenote model
      ((values.map APL.Val.type).mapIdx (fun index type => parameterScalar type (offset + index)))
      (values.map VCG.embed) := by
  induction values generalizing offset with
  | nil => exact .nil
  | cons value values ih =>
      simp only [List.map_cons, List.mapIdx_cons]
      refine .cons (parameterScalar_denotes (by simp) ?_) ?_
      · intro _
        exact hm 0 value rfl
      · have ht := ih (offset + 1) (by
          intro index value hv
          have hh := hm (index + 1) value hv
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

private theorem parameter_value_denote (value : FlatProducts.Val) (offset : Nat)
    (hm : ∀ index leaf, (runtimeLeaves value)[index]? = some leaf →
      model (offset + index) = VCG.embed leaf) :
    RuntimeDenotes model (parameterValue value.type offset) value := by
  cases value with
  | scalar value =>
      refine .scalar (parameterScalar_denotes (by simp) ?_)
      intro _
      simpa using hm 0 value rfl
  | tuple fields =>
      exact .tuple (parameter_fields_denote fields.fields offset hm)

private theorem parameter_layout_denote (values : List FlatProducts.Val) (offset : Nat)
    (hm : ∀ index leaf, (values.flatMap runtimeLeaves)[index]? = some leaf →
      model (offset + index) = VCG.embed leaf) :
    RuntimeEnvRep model (parameterLayout (values.map FlatProducts.Val.type) offset) values := by
  induction values generalizing offset with
  | nil => exact .nil
  | cons value values ih =>
      refine .cons (parameter_value_denote value offset ?_) (ih (offset + leafWidth value.type) ?_)
      · intro index leaf hv
        have hi := (List.getElem?_eq_some_iff.mp hv).1
        apply hm index leaf
        simpa [List.getElem?_append_left hi] using hv
      · intro index leaf hv
        have hh := hm ((runtimeLeaves value).length + index) leaf (by
          simpa only [List.flatMap_cons, List.getElem?_append_right (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left] using hv)
        simpa [runtime_leaves_width, Nat.add_assoc] using hh

theorem parameter_model_rep (ht : values.map FlatProducts.Val.type = types) :
    RuntimeEnvRep (parameterModel values) (parameterLayout types 0) values := by
  subst types
  apply parameter_layout_denote
  intro index leaf hv
  simpa using parameter_model_leaf hv

theorem parameter_entry_exists (ht : values.map FlatProducts.Val.type = types) :
    ∃ model, RuntimeEnvRep model (parameterLayout types 0) values ∧
      (envDomain (parameterLayout types 0)).Holds model := by
  have hr := parameter_model_rep ht
  exact ⟨parameterModel values, hr, env_domain_sound hr⟩

private theorem runtime_type_inhabited (type : FlatProducts.Ty) :
    ∃ value : FlatProducts.Val, value.type = type := by
  have scalar (type : APL.Ty) : ∃ value : APL.Val, value.type = type := by
    cases type with
    | i64 => exact ⟨.int ⟨0, by decide⟩, rfl⟩
    | bool => exact ⟨.bool false, rfl⟩
    | unit => exact ⟨.unit, rfl⟩
  have fields (types : List APL.Ty) : ∃ values : List APL.Val, values.map APL.Val.type = types := by
    induction types with
    | nil => exact ⟨[], rfl⟩
    | cons type types ih =>
        obtain ⟨value, hv⟩ := scalar type
        obtain ⟨values, hvs⟩ := ih
        exact ⟨value :: values, by simp [hv, hvs]⟩
  cases type with
  | scalar type =>
      obtain ⟨value, hv⟩ := scalar type
      exact ⟨.scalar value, congrArg FlatProducts.Ty.scalar hv⟩
  | tuple shape =>
      obtain ⟨values, hv⟩ := fields shape.fields
      have hl : values.length = shape.fields.length := by simpa using congrArg List.length hv
      exact ⟨.tuple ⟨values, by rw [hl]; exact shape.nonempty,
        by rw [hl]; exact shape.bounded⟩,
        congrArg FlatProducts.Ty.tuple (FlatProducts.Flat.ext hv)⟩

theorem parameter_domain_satisfiable (types : List FlatProducts.Ty) :
    ∃ model, (envDomain (parameterLayout types 0)).Holds model := by
  have inhabited : ∃ values : List FlatProducts.Val, values.map FlatProducts.Val.type = types := by
    induction types with
    | nil => exact ⟨[], rfl⟩
    | cons type types ih =>
        obtain ⟨value, hv⟩ := runtime_type_inhabited type
        obtain ⟨values, hvs⟩ := ih
        exact ⟨value :: values, by simp [hv, hvs]⟩
  obtain ⟨values, ht⟩ := inhabited
  obtain ⟨model, _, hd⟩ := parameter_entry_exists ht
  exact ⟨model, hd⟩

theorem parameter_entry_complete (hd : (envDomain (parameterLayout types 0)).Holds model) :
    ∃ values, values.map FlatProducts.Val.type = types ∧
      RuntimeEnvRep model (parameterLayout types 0) values := by
  obtain ⟨values, hr⟩ := env_domain_complete hd
  refine ⟨values, ?_, hr⟩
  have hs := hr.shape
  simpa [List.map_map, Function.comp_def, parameterLayout_shapes] using hs.symm

theorem parameter_entry_iff :
    (envDomain (parameterLayout types 0)).Holds model ↔
      ∃ values, values.map FlatProducts.Val.type = types ∧
        RuntimeEnvRep model (parameterLayout types 0) values := by
  exact ⟨parameter_entry_complete, fun ⟨_, _, hr⟩ => env_domain_sound hr⟩

theorem parameter_initial_support :
    SymbolsBelow (reservedCount types) (parameterLayout types 0) :=
  parameterLayout_supported (by omega)

theorem parameter_layout_length : (parameterLayout types offset).length = types.length := by
  simpa using congrArg List.length (parameterLayout_shapes types offset)

theorem parameter_body_entry (hr : RuntimeEnvRep model (parameterLayout types 0) values) :
    RuntimeEnvRep model (parameterLayout types 0).reverse values.reverse ∧
      FlatProducts.EnvTyped values.reverse (FlatProducts.immutable types.reverse) := by
  constructor
  · change EnvRep model (parameterLayout types 0).reverse (values.reverse.map embedValue)
    rw [List.map_reverse]
    exact hr.reverse
  · have hs : values.map FlatProducts.Val.type = types := by
      simpa [List.map_map, Function.comp_def, parameterLayout_shapes] using hr.shape.symm
    simp [FlatProducts.EnvTyped, FlatProducts.immutable, List.map_map, Function.comp_def, hs]

def displayHeadLogical (start reserved display : Nat) : Nat := reserved + (display - start)

theorem display_head_initial : displayHeadLogical start reserved start = reserved := by
  simp [displayHeadLogical]

theorem display_head_increment (h : start ≤ display) :
    displayHeadLogical start reserved (display + 1) = displayHeadLogical start reserved display + 1 := by
  simp only [displayHeadLogical]
  omega

theorem display_head_injective (ha : start ≤ a) (hb : start ≤ b) :
    displayHeadLogical start reserved a = displayHeadLogical start reserved b ↔ a = b := by
  simp only [displayHeadLogical]
  omega

theorem display_head_order (ha : start ≤ a) (hb : start ≤ b) :
    displayHeadLogical start reserved a < displayHeadLogical start reserved b ↔ a < b := by
  simp only [displayHeadLogical]
  omega

theorem display_head_parameter_disjoint (hslot : SlotValid types parameter field) :
    leafSlot types parameter field < displayHeadLogical start (reservedCount types) display := by
  have hb := leafSlot_in_bounds hslot
  simp only [displayHeadLogical]
  omega

theorem display_head_identity :
    displayHeadLogical start (reservedCount types) display = headIdentity types (display - start) := rfl

end APL.ProductEntry
