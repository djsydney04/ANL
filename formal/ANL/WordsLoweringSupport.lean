import ANL.WordsLowering

namespace ANL.Words.Lowering

variable {sigs : Signatures} {c d : Mir.Context} {f : Fragment} {rest : Arguments}
variable {t : Ty} {supply : Supply} {op : Mir.Operation} {before : List Mir.Instruction}
variable {value : Mir.Temp} {locals : Locals} {resources : List Nat} {Γ : VCtx} {R : RCtx} {index : Nat}

structure Extends (before after : Mir.Context) : Prop where
  temps : ∀ v ∈ before.temps, v ∈ after.temps
  slots : ∀ s ∈ before.slots, s ∈ after.slots
  resources : ∀ r ∈ before.resources, r ∈ after.resources

theorem Extends.refl (c : Mir.Context) : Extends c c := ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩
theorem Extends.trans (h : Extends a b) (g : Extends b c) : Extends a c :=
  ⟨fun v hv => g.temps v (h.temps v hv), fun s hs => g.slots s (h.slots s hs),
    fun r hr => g.resources r (h.resources r hr)⟩

theorem Extends.withTemp (c : Mir.Context) (v : Mir.Temp) : Extends c (c.withTemp v) :=
  ⟨fun _ h => .tail _ h, fun _ h => h, fun _ h => h⟩
theorem Extends.withSlot (c : Mir.Context) (s : Mir.Slot) : Extends c (c.withSlot s) :=
  ⟨fun _ h => h, fun _ h => .tail _ h, fun _ h => h⟩
theorem Extends.withOwner (c : Mir.Context) (r : Nat) : Extends c (c.withOwner r) :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => .tail _ h⟩

def advance (c : Mir.Context) : List Mir.Instruction → Mir.Context
  | [] => c
  | i :: rest => advance (c.withTemp i.destination) rest

theorem advance_append (c : Mir.Context) (a b : List Mir.Instruction) :
    advance c (a ++ b) = advance (advance c a) b := by
  induction a generalizing c <;> simp_all [advance]

theorem advance_extends (c : Mir.Context) (instructions : List Mir.Instruction) :
    Extends c (advance c instructions) := by
  induction instructions generalizing c with
  | nil => exact .refl c
  | cons i rest ih => exact (Extends.withTemp c i.destination).trans (ih _)

def InstructionsTyped (sigs : Signatures) (c : Mir.Context) : List Mir.Instruction → Prop
  | [] => True
  | i :: rest => i.operation.Typed sigs c i.destination.ty ∧
      InstructionsTyped sigs (c.withTemp i.destination) rest

theorem instructions_append_iff (sigs : Signatures) (c : Mir.Context) (a b : List Mir.Instruction) :
    InstructionsTyped sigs c (a ++ b) ↔
      InstructionsTyped sigs c a ∧ InstructionsTyped sigs (advance c a) b := by
  induction a generalizing c <;> simp_all [InstructionsTyped, advance, and_assoc]

theorem instructions_block_iff (sigs : Signatures) (c : Mir.Context) (instructions : List Mir.Instruction)
    (value : Mir.Temp) (t : Ty) :
    (Mir.Block.fromInstructions instructions value).Typed sigs c t ↔
      InstructionsTyped sigs c instructions ∧ value.Typed (advance c instructions) t := by
  induction instructions generalizing c with
  | nil => simp [Mir.Block.fromInstructions, Mir.Block.Typed, InstructionsTyped, advance]
  | cons i rest ih =>
      simp only [Mir.Block.fromInstructions, List.foldr_cons, Mir.Block.Typed]
      change _ ∧ (Mir.Block.fromInstructions rest value).Typed sigs _ t ↔ _
      rw [ih]
      simp [InstructionsTyped, advance, and_assoc]

def Fragment.Typed (sigs : Signatures) (c : Mir.Context) (f : Fragment) (t : Ty) : Prop :=
  InstructionsTyped sigs c f.instructions ∧ f.value.Typed (advance c f.instructions) t

def Arguments.Typed (sigs : Signatures) (c : Mir.Context) (args : Arguments) (types : List Ty) : Prop :=
  InstructionsTyped sigs c args.instructions ∧ Mir.ArgsTyped (advance c args.instructions) args.values types

theorem Fragment.Typed.block (h : f.Typed sigs c t) : f.block.Typed sigs c t :=
  (instructions_block_iff ..).mpr h

theorem Fragment.Typed.prefix (hbefore : InstructionsTyped sigs c before)
    (h : f.Typed sigs (advance c before) t) : (f.prefix before).Typed sigs c t := by
  exact ⟨(instructions_append_iff ..).mpr ⟨hbefore, h.1⟩,
    by simpa [Fragment.prefix, advance_append] using h.2⟩

theorem emit_typed (hbefore : InstructionsTyped sigs c before)
    (hop : op.Typed sigs (advance c before) t) : (emit t op before supply).1.Typed sigs c t := by
  simp [emit, Fragment.Typed, instructions_append_iff, hbefore, hop, InstructionsTyped,
    advance_append, advance, Mir.Temp.Typed, Mir.Context.withTemp]

theorem temp_weaken {v : Mir.Temp} (h : v.Typed c t) (hc : Extends c d) : v.Typed d t :=
  ⟨hc.temps _ h.1, h.2⟩

theorem args_cons {v : Mir.Temp} (h : v.Typed c t) (rest : Mir.ArgsTyped c vs ts) :
    Mir.ArgsTyped c (v :: vs) (t :: ts) := by
  constructor
  · intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact rest.1 _ hv
  · simp [h.2, rest.2]

theorem arguments_cons_typed (head : f.Typed sigs c t)
    (tail : rest.Typed sigs (advance c f.instructions) ts) :
    (Arguments.mk (f.instructions ++ rest.instructions) (f.value :: rest.values)).Typed sigs c (t :: ts) := by
  constructor
  · exact (instructions_append_iff ..).mpr ⟨head.1, tail.1⟩
  · simp only [advance_append]
    exact args_cons (temp_weaken head.2 (advance_extends _ _)) tail.2

def Local.spec : Local → Ty × Bool
  | .value v => (v.ty, false)
  | .mutable s => (s.ty, true)

def Local.Visible (c : Mir.Context) : Local → Prop
  | .value v => v ∈ c.temps
  | .mutable s => s ∈ c.slots

theorem Local.Visible.weaken {l : Local} (h : l.Visible c) (hc : Extends c d) : l.Visible d := by
  cases l with
  | value v => exact hc.temps v h
  | mutable s => exact hc.slots s h

inductive ResourceRep (c : Mir.Context) : List Nat → RCtx → Prop where
  | nil : ResourceRep c [] []
  | cons {resource : Nat} {mode : Mode} {resources : List Nat} {modes : RCtx} :
      (resource, mode) ∈ c.resources → ResourceRep c resources modes →
      ResourceRep c (resource :: resources) (mode :: modes)

theorem ResourceRep.weaken (h : ResourceRep c resources R) (hc : Extends c d) :
    ResourceRep d resources R := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hc.resources _ hr) ih

theorem ResourceRep.lookup (h : ResourceRep c resources R) (hi : R[index]? = some mode) :
    ∃ resource, resources[index]? = some resource ∧ (resource, mode) ∈ c.resources := by
  induction h generalizing index with
  | nil => simp at hi
  | cons binding _ ih =>
      cases index with
      | zero => simp_all
      | succ index => exact ih (by simpa using hi)

structure Represented (c : Mir.Context) (locals : Locals) (resources : List Nat) (Γ : VCtx) (R : RCtx) : Prop where
  localTypes : locals.map Local.spec = Γ
  localVisible : ∀ l ∈ locals, l.Visible c
  resourceBindings : ResourceRep c resources R

theorem Represented.weaken (h : Represented c locals resources Γ R) (hc : Extends c d) :
    Represented d locals resources Γ R := by
  exact ⟨h.localTypes, fun l hl => (h.localVisible l hl).weaken hc, h.resourceBindings.weaken hc⟩

theorem Represented.local_lookup (h : Represented c locals resources Γ R)
    (hi : Γ[index]? = some (t, permission)) :
    ∃ l, locals[index]? = some l ∧ l.spec = (t, permission) ∧ l.Visible c := by
  rw [← h.localTypes, List.getElem?_map] at hi
  obtain ⟨l, hl, ht⟩ := Option.map_eq_some_iff.mp hi
  exact ⟨l, hl, ht, h.localVisible l (List.mem_of_getElem? hl)⟩

theorem Represented.resource_lookup (h : Represented c locals resources Γ R)
    (hi : R[index]? = some mode) :
    ∃ resource, resources[index]? = some resource ∧ (resource, mode) ∈ c.resources := by
  exact h.resourceBindings.lookup hi

theorem Represented.withValue (h : Represented c locals resources Γ R) (hv : value.Typed c t) :
    Represented c (.value value :: locals) resources ((t, false) :: Γ) R := by
  refine ⟨by simp [Local.spec, h.localTypes, hv.2], ?_, h.resourceBindings⟩
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact hv.1
  · exact h.localVisible l hl

theorem Represented.withMutable (h : Represented c locals resources Γ R) (slot : Mir.Slot) :
    Represented (c.withSlot slot) (.mutable slot :: locals) resources ((slot.ty, true) :: Γ) R := by
  have old := h.weaken (Extends.withSlot c slot)
  refine ⟨by simp [Local.spec, old.localTypes], ?_, old.resourceBindings⟩
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact .head _
  · exact old.localVisible l hl

theorem Represented.withOwner (h : Represented c locals resources Γ R) (owner : Nat) :
    Represented (c.withOwner owner) locals (owner :: resources) Γ (.owner :: R) := by
  have old := h.weaken (Extends.withOwner c owner)
  exact ⟨old.localTypes, old.localVisible, .cons (.head _) old.resourceBindings⟩

end ANL.Words.Lowering
