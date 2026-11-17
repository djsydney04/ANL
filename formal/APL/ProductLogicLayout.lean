import APL.ProductLogicValues

namespace APL.ProductLogic

open FlatProducts (Flat)

def leafTypes : FlatProducts.Ty → List APL.Ty
  | .scalar type => [type]
  | .tuple shape => shape.fields

def leafWidth (type : FlatProducts.Ty) : Nat := (leafTypes type).length

def reservedCount : List FlatProducts.Ty → Nat
  | [] => 0
  | type :: rest => leafWidth type + reservedCount rest

def parameterOffset : List FlatProducts.Ty → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | type :: rest, index + 1 => leafWidth type + parameterOffset rest index

def leafSlot (parameters : List FlatProducts.Ty) (parameter field : Nat) : Nat :=
  parameterOffset parameters parameter + field

def SlotValid (parameters : List FlatProducts.Ty) (parameter field : Nat) : Prop :=
  ∃ type, parameters[parameter]? = some type ∧ field < leafWidth type

def nonUnitCount (parameters : List FlatProducts.Ty) : Nat :=
  ((parameters.flatMap leafTypes).filter (· != .unit)).length

def headIdentity (parameters : List FlatProducts.Ty) (allocatedHead : Nat) : Nat :=
  reservedCount parameters + allocatedHead

theorem leafWidth_positive (type : FlatProducts.Ty) : 0 < leafWidth type := by
  cases type with
  | scalar => simp [leafWidth, leafTypes]
  | tuple shape => exact shape.nonempty

theorem leafSlot_in_bounds (h : SlotValid parameters parameter field) :
    leafSlot parameters parameter field < reservedCount parameters := by
  induction parameters generalizing parameter with
  | nil => obtain ⟨_, h, _⟩ := h; simp at h
  | cons type rest ih =>
      cases parameter with
      | zero =>
          obtain ⟨_, he, hb⟩ := h
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst type
          simp only [leafSlot, parameterOffset, Nat.zero_add, reservedCount]
          omega
      | succ parameter =>
          have ht : SlotValid rest parameter field := h
          have bound := ih ht
          simp only [leafSlot, parameterOffset, reservedCount] at bound ⊢
          omega

theorem leafSlot_unique (ha : SlotValid parameters pa fa) (hb : SlotValid parameters pb fb)
    (he : leafSlot parameters pa fa = leafSlot parameters pb fb) : pa = pb ∧ fa = fb := by
  induction parameters generalizing pa pb with
  | nil => obtain ⟨_, h, _⟩ := ha; simp at h
  | cons type rest ih =>
      cases pa with
      | zero =>
          obtain ⟨ta, hta, hfa⟩ := ha
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hta
          subst ta
          cases pb with
          | zero => simp only [leafSlot, parameterOffset, Nat.zero_add] at he; exact ⟨rfl, he⟩
          | succ pb => simp only [leafSlot, parameterOffset, Nat.zero_add] at he; omega
      | succ pa =>
          cases pb with
          | zero =>
              obtain ⟨tb, htb, hfb⟩ := hb
              simp only [List.getElem?_cons_zero, Option.some.injEq] at htb
              subst tb
              simp only [leafSlot, parameterOffset, Nat.zero_add] at he
              omega
          | succ pb =>
              have he' : leafSlot rest pa fa = leafSlot rest pb fb := by
                simp only [leafSlot, parameterOffset] at he ⊢
                omega
              obtain ⟨hp, hf⟩ := ih ha hb he'
              exact ⟨congrArg Nat.succ hp, hf⟩

theorem headIdentity_disjoint (h : SlotValid parameters parameter field) :
    leafSlot parameters parameter field < headIdentity parameters allocatedHead := by
  have hb := leafSlot_in_bounds h
  simp only [headIdentity]
  omega

theorem headIdentity_injective : headIdentity parameters a = headIdentity parameters b ↔ a = b := by
  simp [headIdentity]

@[simp] theorem scalar_reservedCount (types : List APL.Ty) :
    reservedCount (types.map FlatProducts.Ty.scalar) = types.length := by
  induction types with
  | nil => rfl
  | cons type rest ih => simp [reservedCount, leafWidth, leafTypes, ih, Nat.add_comm]

theorem scalar_parameterOffset (types : List APL.Ty) (h : parameter ≤ types.length) :
    parameterOffset (types.map FlatProducts.Ty.scalar) parameter = parameter := by
  induction types generalizing parameter with
  | nil =>
      have : parameter = 0 := by simpa using h
      subst parameter
      rfl
  | cons type rest ih =>
      cases parameter with
      | zero => rfl
      | succ parameter =>
          have hb : parameter ≤ rest.length := by simpa using h
          simp [parameterOffset, leafWidth, leafTypes, ih hb, Nat.add_comm]

theorem scalar_leafSlot (types : List APL.Ty) (h : parameter < types.length) :
    leafSlot (types.map FlatProducts.Ty.scalar) parameter 0 = parameter := by
  simp [leafSlot, scalar_parameterOffset types (Nat.le_of_lt h)]

def parameterScalar (type : APL.Ty) (slot : Nat) : SymScalar :=
  ⟨type, if type = .unit then .lit .unit else .var slot, by intro h; simp [h]⟩

@[simp] theorem parameterScalar_type : (parameterScalar type slot).type = type := rfl

@[simp] theorem parameterScalar_unit (slot : Nat) :
    (parameterScalar .unit slot).term = .lit .unit := by simp [parameterScalar]

theorem parameterScalar_nonunit (h : type ≠ .unit) :
    (parameterScalar type slot).term = .var slot := by simp [parameterScalar, h]

theorem parameterScalar_supported (h : slot < bound) : (parameterScalar type slot).Supported bound := by
  by_cases hu : type = .unit
  · simp [SymScalar.Supported, parameterScalar, hu, SymTerm.Supported]
  · simpa [SymScalar.Supported, parameterScalar, hu, SymTerm.Supported] using h

def parameterValue (type : FlatProducts.Ty) (offset : Nat) : SymValue :=
  match type with
  | .scalar type => .scalar (parameterScalar type offset)
  | .tuple shape => .tuple
      ⟨shape.fields.mapIdx (fun field type => parameterScalar type (offset + field)),
        by simpa using shape.nonempty, by simpa using shape.bounded⟩

def parameterLayout : List FlatProducts.Ty → Nat → List SymValue
  | [], _ => []
  | type :: rest, offset => parameterValue type offset :: parameterLayout rest (offset + leafWidth type)

theorem parameterValue_shape (type : FlatProducts.Ty) (offset : Nat) :
    (parameterValue type offset).type = type := by
  cases type with
  | scalar => rfl
  | tuple shape =>
      simp only [parameterValue, SymValue.type]
      congr 1
      apply Flat.ext
      apply List.ext_getElem
      · simp [Flat.map]
      · intro i hi hj
        simp [Flat.map]

theorem parameterLayout_shapes (types : List FlatProducts.Ty) (offset : Nat) :
    (parameterLayout types offset).map SymValue.type = types := by
  induction types generalizing offset with
  | nil => rfl
  | cons type rest ih => simp [parameterLayout, parameterValue_shape, ih]

theorem parameterValue_supported (h : offset + leafWidth type ≤ bound) :
    (parameterValue type offset).Supported bound := by
  cases type with
  | scalar type =>
      apply parameterScalar_supported
      simp only [leafWidth, leafTypes, List.length_singleton] at h
      omega
  | tuple shape =>
      intro field hf
      obtain ⟨index, hi, rfl⟩ := List.mem_mapIdx.mp hf
      apply parameterScalar_supported
      change offset + shape.fields.length ≤ bound at h
      omega

theorem parameterLayout_supported (h : offset + reservedCount types ≤ bound) :
    ∀ value ∈ parameterLayout types offset, value.Supported bound := by
  induction types generalizing offset with
  | nil => simp [parameterLayout]
  | cons type rest ih =>
      intro value hv
      simp only [parameterLayout, List.mem_cons] at hv
      simp only [reservedCount] at h
      rcases hv with rfl | hv
      · exact parameterValue_supported (by omega)
      · exact ih (by omega) value hv

theorem parameterLayout_lookup (h : types[(parameter : Nat)]? = some type) :
    (parameterLayout types offset)[parameter]? =
      some (parameterValue type (offset + parameterOffset types parameter)) := by
  induction types generalizing offset parameter with
  | nil => simp at h
  | cons head rest ih =>
      cases parameter with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst type
          simp [parameterLayout, parameterOffset]
      | succ parameter =>
          simpa [parameterLayout, parameterOffset, Nat.add_assoc] using
            ih (offset := offset + leafWidth head) h

theorem parameter_tuple_field (h : shape.fields[(field : Nat)]? = some type) :
    project (parameterValue (.tuple shape) offset) field = some (parameterScalar type (offset + field)) := by
  simp [parameterValue, project, h]

theorem parameterScalar_denotes (ht : value.type = type)
    (hm : type ≠ .unit → model slot = value) : ScalarDenotes model (parameterScalar type slot) value := by
  refine ⟨ht.symm, ?_⟩
  by_cases hu : type = .unit
  · have hv : value = .unit := by cases value <;> simp_all [VCG.MVal.type]
    simp [parameterScalar, hu, hv, SymTerm.eval]
  · simp [parameterScalar, hu, SymTerm.eval, hm hu]

end APL.ProductLogic
