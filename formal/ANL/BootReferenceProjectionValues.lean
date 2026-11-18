import ANL.BootReferenceProjection
import ANL.BootRuntimeEffectCompletion

namespace ANL.Boot.Reference.Projection
open ANL.Words ANL.Boot.Runtime ANL.Boot.Runtime.Session

 theorem ValueOf.compute (meaning : ValueOf raw view) : valueView raw = some view := by
  cases meaning with
  | unit => simp [valueView]
  | byte value => cases value; simp [valueView, byteOperand, unitValue]

 theorem valueView_iff : valueView raw = some view ↔ ValueOf raw view := by
  constructor
  · intro found
    unfold valueView at found
    split at found
    next equal => subst raw; cases found; exact .unit
    next different =>
      obtain ⟨n, byte, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .byte (byteOperand_iff.mp byte)
  · exact ValueOf.compute

 theorem ArgumentsOf.compute (meaning : ArgumentsOf op raw view) : argumentViews op raw = some view := by
  cases meaning with
  | empty empty => cases op <;> simp_all [Operation.params, argumentViews]
  | write byte => cases byte; simp [argumentViews, byteOperand]

 theorem argumentViews_iff : argumentViews op raw = some view ↔ ArgumentsOf op raw view := by
  constructor
  · intro found
    unfold argumentViews at found
    split at found
    next region offset value =>
      obtain ⟨n, byte, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .write (byteOperand_iff.mp byte)
    next => contradiction
    next _ _ notWrite =>
      cases found
      apply ArgumentsOf.empty
      cases op <;> first | rfl | exact False.elim (notWrite _ _ rfl)
    next => contradiction
  · exact ArgumentsOf.compute

 theorem PendingOf.compute (meaning : PendingOf raw view) : pendingView raw = some view := by
  rcases raw with ⟨ordinal, declaration, op, args, origin⟩
  rcases view with ⟨n, id, operation, values, location⟩
  rcases meaning with ⟨rfl, rfl, rfl, arguments, rfl⟩
  simp [pendingView, arguments.compute]

 theorem pendingView_iff : pendingView raw = some view ↔ PendingOf raw view := by
  constructor
  · intro found
    simp only [pendingView, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨args, found, rfl⟩ := found
    exact ⟨rfl, rfl, rfl, argumentViews_iff.mp found, rfl⟩
  · exact PendingOf.compute

 theorem PhaseOf.compute (meaning : PhaseOf raw view) : phaseView raw = some view := by
  cases meaning with
  | ordinary => rfl
  | parkCheck => rfl
  | parkObserved => rfl
  | before pending => simp [phaseView, pending.compute]
  | commit pending => simp [phaseView, pending.compute]
  | after pending value => simp [phaseView, pending.compute, value.compute]
  | finish pending value => simp [phaseView, pending.compute, value.compute]

 theorem phaseView_iff : phaseView raw = some view ↔ PhaseOf raw view := by
  constructor
  · intro found
    cases raw with
    | ordinary => cases found; exact .ordinary
    | parkCheck location => cases found; exact .parkCheck
    | parkObserved location => cases found; exact .parkObserved
    | primitiveBefore q =>
      obtain ⟨v, h, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .before (pendingView_iff.mp h)
    | primitiveCommit q =>
      obtain ⟨v, h, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .commit (pendingView_iff.mp h)
    | primitiveAfter q v =>
      simp only [phaseView, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
      obtain ⟨qv, hq, vv, hv, rfl⟩ := found
      exact .after (pendingView_iff.mp hq) (valueView_iff.mp hv)
    | primitiveReturn q v =>
      simp only [phaseView, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
      obtain ⟨qv, hq, vv, hv, rfl⟩ := found
      exact .finish (pendingView_iff.mp hq) (valueView_iff.mp hv)
  · exact PhaseOf.compute

 theorem ValueOf.bounded (meaning : ValueOf raw view) : ValueEncodable view := by
  cases meaning with
  | unit => trivial
  | byte byte => exact byte.bound

 theorem ArgumentsOf.bounded (meaning : ArgumentsOf op raw view) : ArgumentsEncodable op view := by
  cases meaning with
  | empty empty => simp [ArgumentsEncodable, empty]
  | write byte => simp [ArgumentsEncodable, Operation.params, ByteEncodable, byte.bound]

 theorem unit_typed (typed : raw.type = unitTy) : raw = unitValue := by
  cases raw with
  | tuple _ => cases typed
  | scalar scalar => cases scalar with
    | word _ => cases typed
    | legacy value => cases value <;> cases typed; rfl

 theorem result_representable (typed : raw.type = op.result) : ∃ view, ValueOf raw view ∧ ResultEncodable op view := by
  cases op with
  | read8 region offset =>
    obtain ⟨n, byte⟩ := byte_typed typed
    exact ⟨.byte n, .byte byte, byte.bound⟩
  | write8 | fence | csrClear | csrWrite | installTrap =>
    have equal := unit_typed typed
    subst raw
    exact ⟨.unit, .unit, trivial⟩

 theorem arguments_representable (typed : raw.map Words.Val.type = op.params) : ∃ view, ArgumentsOf op raw view := by
  cases op with
  | write8 region offset =>
    obtain ⟨n, value, rfl, byte⟩ := typed_write_arguments typed
    exact ⟨[.byte n], .write byte⟩
  | read8 | fence | csrClear | csrWrite | installTrap =>
    have empty : raw = [] := List.map_eq_nil_iff.mp typed
    subst raw
    exact ⟨[], .empty rfl⟩

 theorem pending_representable (pending : PendingAt p state q) : ∃ view, PendingOf q view := by
  obtain ⟨args, meaning⟩ := arguments_representable pending.2.2.2.2.1
  exact ⟨⟨q.ordinal, q.declaration, q.operation, args, q.origin⟩, rfl, rfl, rfl, meaning, rfl⟩

 theorem phase_representable (invariant : PhaseInvariant p state) : ∃ view, PhaseOf state.phase view := by
  cases invariant with
  | ordinary equal => rw [equal]; exact ⟨.ordinary, .ordinary⟩
  | before equal valid =>
    obtain ⟨view, meaning⟩ := pending_representable valid.1
    rw [equal]; exact ⟨.before view, .before meaning⟩
  | commit equal valid =>
    obtain ⟨view, meaning⟩ := pending_representable valid.1
    rw [equal]; exact ⟨.commit view, .commit meaning⟩
  | after equal valid _ =>
    obtain ⟨view, meaning⟩ := pending_representable valid.1
    obtain ⟨value, result, _⟩ := result_representable valid.2.2
    rw [equal]; exact ⟨.after view value, .after meaning result⟩
  | finish equal valid _ =>
    obtain ⟨view, meaning⟩ := pending_representable valid.1
    obtain ⟨value, result, _⟩ := result_representable valid.2.2
    rw [equal]; exact ⟨.finish view value, .finish meaning result⟩
  | parkWaiting equal _ => rw [equal]; exact ⟨_, .parkCheck⟩
  | parkConsumed equal _ => rw [equal]; exact ⟨_, .parkObserved⟩

end ANL.Boot.Reference.Projection
