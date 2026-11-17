import ANL.MemorySimulationData

namespace ANL.Memory.Simulation

/-- These MIR steps only expose the next operation or carry an already produced value. -/
inductive MirAdmin : Mir.State → Mir.State → Prop where
  | block : MirAdmin ⟨.block body, a, k, w⟩ ⟨.sequence body, a, .blockEnd a.temps :: k, w⟩
  | instruction : MirAdmin ⟨.sequence (.next d op rest), a, k, w⟩
      ⟨.operation op, a, .instruction d rest :: k, w⟩
  | yieldFound : a.temp t = some v →
      MirAdmin ⟨.sequence (.yield t), a, k, w⟩ ⟨.ret v, a, k, w⟩
  | yieldMissing : a.temp t = none →
      MirAdmin ⟨.sequence (.yield t), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | destination : MirAdmin ⟨.ret v, a, .instruction d rest :: k, w⟩
      ⟨.sequence rest, {a with temps := (d.id, v) :: a.temps}, k, w⟩
  | blockEnd : MirAdmin ⟨.ret v, a, .blockEnd temps :: k, w⟩
      ⟨.ret v, {a with temps}, k, w⟩

def mirAdminRank (s : Mir.State) : Nat := match s.control with
  | .block _ => 5 * s.kont.length + 9
  | .sequence _ => 5 * s.kont.length + 3
  | .ret _ => 5 * s.kont.length
  | _ => 0

theorem MirAdmin.rank (h : MirAdmin a b) : mirAdminRank b < mirAdminRank a := by
  cases h <;> simp [mirAdminRank] <;> omega

theorem MirAdmin.step (h : MirAdmin a b) : Mir.Step p responses a b := by
  cases h with
  | block => exact .block
  | instruction => exact .instruction
  | yieldFound h => exact .yieldFound h
  | yieldMissing h => exact .yieldMissing h
  | destination => exact .instructionReturn
  | blockEnd => exact .blockReturn

theorem MirAdmin.retains (h : MirAdmin a b) :
    a.world = b.world ∧ a.current.function = b.current.function ∧
    a.current.slots = b.current.slots ∧ a.current.resources = b.current.resources := by
  cases h <;> exact ⟨rfl, rfl, rfl, rfl⟩

inductive MirAdmins : Mir.State → Mir.State → Prop where
  | refl : MirAdmins a a
  | cons : MirAdmin a b → MirAdmins b c → MirAdmins a c

theorem MirAdmins.steps (h : MirAdmins a b) : Mir.Steps p responses a b := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons h.step ih

def mirAdminStep (s : Mir.State) : Option Mir.State :=
  match s.control, s.kont with
  | .block body, _ => some ⟨.sequence body, s.current, .blockEnd s.current.temps :: s.kont, s.world⟩
  | .sequence (.next d op rest), _ => some ⟨.operation op, s.current, .instruction d rest :: s.kont, s.world⟩
  | .sequence (.yield t), _ => some (match s.current.temp t with
      | some v => ⟨.ret v, s.current, s.kont, s.world⟩
      | none => ⟨.invalid, s.current, s.kont, s.world⟩)
  | .ret v, .instruction d rest :: k => some ⟨.sequence rest, {s.current with temps := (d.id, v) :: s.current.temps}, k, s.world⟩
  | .ret v, .blockEnd temps :: k => some ⟨.ret v, {s.current with temps}, k, s.world⟩
  | _, _ => none

theorem mirAdminStep_complete (h : MirAdmin s t) : mirAdminStep s = some t := by
  cases h <;> simp_all [mirAdminStep]

theorem mirAdminStep_sound (h : mirAdminStep s = some t) : MirAdmin s t := by
  rcases s with ⟨control, a, k, w⟩
  cases control with
  | block body => simp only [mirAdminStep, Option.some.injEq] at h; subst t; exact .block
  | sequence body =>
      cases body with
      | next d op rest => simp only [mirAdminStep, Option.some.injEq] at h; subst t; exact .instruction
      | yield value =>
          cases hv : a.temp value <;> simp only [mirAdminStep, hv, Option.some.injEq] at h
          · subst t; exact .yieldMissing hv
          · subst t; exact .yieldFound hv
  | ret value =>
      cases k with
      | nil => simp [mirAdminStep] at h
      | cons frame rest =>
          cases frame <;> simp only [mirAdminStep, Option.some.injEq, reduceCtorEq] at h
          all_goals subst t
          all_goals first | exact .destination | exact .blockEnd
  | _ => simp [mirAdminStep] at h

theorem mirAdminStep_iff : mirAdminStep s = some t ↔ MirAdmin s t :=
  ⟨mirAdminStep_sound, mirAdminStep_complete⟩

/-- Total structural normalization; no semantic allocation or call is performed here. -/
def normalizeMir (s : Mir.State) : Mir.State :=
  match _h : mirAdminStep s with
  | none => s
  | some next => normalizeMir next
termination_by mirAdminRank s
decreasing_by exact (mirAdminStep_sound _h).rank

theorem normalizeMir_spec (s : Mir.State) :
    MirAdmins s (normalizeMir s) ∧ mirAdminStep (normalizeMir s) = none := by
  induction s using normalizeMir.induct with
  | case1 s h =>
      have hn : normalizeMir s = s := by rw [normalizeMir, h]
      rw [hn]
      exact ⟨.refl, h⟩
  | case2 s next h ih =>
      rw [normalizeMir, h]
      exact ⟨.cons (mirAdminStep_sound h) ih.1, ih.2⟩

end ANL.Memory.Simulation
