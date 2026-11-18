import ANL.BootRuntimeFrontiers

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem capture_iff : capture p s = some q ↔ Captured p s q := by
  constructor
  · intro found
    unfold capture at found
    split at found
    next ident values controlEq =>
      split at found
      next row declaration =>
        dsimp only at found
        split at found
        next valid =>
          simp only [Option.some.injEq] at found
          subst q
          exact .invoke controlEq declaration valid
        next => cases found
      next => cases found
    next => cases found
  · intro captured
    cases captured with | invoke controlEq declaration valid => simp [capture, controlEq, declaration, valid]

 theorem Captured.valid (h : Captured p s q) : PendingAt p s q := by cases h; assumption
 theorem Captured.ordinal (h : Captured p s q) : q.ordinal = s.nextOrdinal := by cases h; rfl
 theorem Captured.origin (h : Captured p s q) : q.origin = s.origins.control := by cases h; rfl
 theorem Captured.frontier (h : Captured p s q) : Origin.PrimitiveFrontier p s.machine := by
  cases h with | invoke controlEq declaration _ => exact ⟨_, _, _, controlEq, declaration⟩
 theorem Captured.unique (a : Captured p s q) (b : Captured p s r) : q = r :=
  Option.some.inj ((capture_iff.mpr a).symm.trans (capture_iff.mpr b))

 theorem SelectedPark.unique (a : SelectedPark p episode x) (b : SelectedPark p episode y) : x = y :=
  Option.some.inj ((selectedLocation_iff.mpr a).symm.trans (selectedLocation_iff.mpr b))
 theorem SelectedPark.located (a : SelectedPark p episode location) : Origin.Located p location park := by
  cases a with | role found tail => exact Origin.designatedTail_located found tail.search
 theorem ParkControl.eq {ctl : Control} (a : ParkControl ctl) : ctl = .eval park := by
  cases ctl <;> try contradiction
  cases a
  rfl
 theorem ParkAt.exact (a : ParkAt p s location) :
    s.machine.control = .eval park ∧ Origin.Located p location park ∧
      location = s.origins.control ∧ location.function = s.machine.current.function :=
  ⟨a.2.2.2.eq, a.2.2.1.located, a.1, a.2.1⟩

 theorem deliveryAt_iff : deliveryAt env s key = some d ↔ DeliveryAt env s key d := by
  constructor
  · intro found
    unfold deliveryAt at found
    split at found
    next => cases found
    next unused =>
      have unused' : s.deliveryUsed = false := by cases h : s.deliveryUsed <;> simp_all
      split at found
      next value supplied =>
        split at found
        next matching =>
          simp only [Option.some.injEq] at found
          subst d
          exact .matchKey unused' supplied matching
        next => cases found
      next => cases found
  · intro meaning
    cases meaning with | matchKey unused supplied matching => simp [deliveryAt, unused, supplied, matching]

 theorem DeliveryAt.unique (a : DeliveryAt env s key x) (b : DeliveryAt env s key y) : x = y :=
  Option.some.inj ((deliveryAt_iff.mpr a).symm.trans (deliveryAt_iff.mpr b))
 theorem DeliveryAt.unused (a : DeliveryAt env s key d) : s.deliveryUsed = false := by cases a; assumption
 theorem DeliveryAt.landmark_eq (a : DeliveryAt env s key d) : d.landmark = key := by cases a; assumption
 theorem DeliveryAt.valid (input : InputValid p env) (a : DeliveryAt env s key d) : DeliveryValid p d := by
  cases a with | matchKey _ supplied _ => exact input.delivery_valid supplied
 theorem deliveryAt_none_iff : deliveryAt env s key = none ↔ ∀ d, ¬ DeliveryAt env s key d := by
  constructor
  · intro absent d present
    rw [deliveryAt_iff.mpr present] at absent
    cases absent
  · intro absent
    cases found : deliveryAt env s key with
    | none => rfl
    | some d => exact False.elim (absent d (deliveryAt_iff.mp found))

 theorem observedPark_retains :
    (observedPark s location).machine = s.machine ∧
    (observedPark s location).origins = s.origins ∧
    (observedPark s location).hardware = s.hardware ∧
    (observedPark s location).readCursor = s.readCursor ∧
    (observedPark s location).revEvents = s.revEvents ∧
    (observedPark s location).episodeParkSeen = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.Runtime
