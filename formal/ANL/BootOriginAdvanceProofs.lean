import ANL.BootOriginAdvance

namespace ANL.Boot.Origin
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem applyAction_iff : applyAction a m = some n ↔ Applies a m n := by
  constructor
  · cases a <;> cases m with
    | mk ctl frames =>
      cases frames <;> simp only [applyAction, Option.some.injEq, reduceCtorEq]
      all_goals intro h; cases h <;> constructor
  · intro h; cases h <;> rfl

 theorem not_bool {v : Val} (yes : v ≠ .scalar (.legacy (.bool true)))
    (no : v ≠ .scalar (.legacy (.bool false))) : v.type ≠ .scalar (.legacy .bool) := by
  intro h
  obtain ⟨s, rfl, hs⟩ := scalar_canonical h
  obtain ⟨s, rfl, hs⟩ := scalar_legacy_canonical hs
  cases s with
  | bool b => cases b <;> contradiction
  | int | unit => cases hs

 theorem not_unit {v : Val} (no : v ≠ .scalar (.legacy .unit)) : v.type ≠ .scalar (.legacy .unit) := by
  intro h
  obtain ⟨s, rfl, hs⟩ := scalar_canonical h
  obtain ⟨s, rfl, hs⟩ := scalar_legacy_canonical hs
  cases s with
  | unit => contradiction
  | int | bool => cases hs

 theorem Chooses.complete (h : Chooses s.control s.kont next.control a) : action s next = some a := by
  cases s with | mk ctl current kont world =>
   cases next with | mk next nextCurrent nextKont nextWorld =>
    cases h <;> simp_all [action]
    all_goals split <;> simp_all [Val.type, ScalarVal.type, APL.Val.type]

 theorem action_sound (h : action s next = some a) : Chooses s.control s.kont next.control a := by
  unfold action at h
  repeat' first | split at h | (simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals try contradiction
  all_goals subst a
  all_goals simp_all only
  all_goals first
    | (constructor <;> assumption)
    | (constructor <;> first | exact not_bool (by assumption) (by assumption) | exact not_unit (by assumption) | simp_all)

 theorem advance_iff : advance s next m = some n ↔
    ∃ a, Chooses s.control s.kont next.control a ∧ Applies a m n := by
  constructor
  · intro h
    unfold advance at h
    cases ha : action s next with
    | none => simp [ha] at h
    | some a =>
      have hn : applyAction a m = some n := by simpa [ha] using h
      exact ⟨a, action_sound ha, applyAction_iff.mp hn⟩
  · rintro ⟨a, ha, hn⟩
    simp [advance, ha.complete, applyAction_iff.mpr hn]

 theorem step_iff : step p responses s m = some (next, n) ↔ Step p responses s m next n := by
  constructor
  · intro h
    unfold step at h
    split at h
    next allowed =>
      cases hs : ANL.Words.step p.carrier responses s with
      | none => simp [hs] at h
      | some actual =>
        cases hm : advance s actual m with
        | none => simp [hs, hm] at h
        | some result =>
          have eq : actual = next ∧ result = n := by simpa [hs, hm] using h
          rcases eq with ⟨rfl, rfl⟩
          obtain ⟨a, choice, move⟩ := advance_iff.mp hm
          exact .ordinary (checkAdmitted_iff.mp allowed) (ANL.Words.step_sound hs) choice move
    next denied => cases h
  · rintro ⟨allowed, hs, choice, move⟩
    simp [step, checkAdmitted_iff.mpr allowed, ANL.Words.step_complete hs,
      advance_iff.mpr ⟨_, choice, move⟩]

 theorem Step.erase (h : Step p responses s m next n) : ANL.Words.Step p.carrier responses s next := by
  cases h; assumption

 theorem Step.deterministic (h : Step p responses s m next n) (h' : Step p responses s m next' n') :
    next = next' ∧ n = n' := by
  have eq := (step_iff.mpr h).symm.trans (step_iff.mpr h')
  simpa only [Option.some.injEq, Prod.mk.injEq] using eq

end ANL.Boot.Origin
