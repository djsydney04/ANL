import APL.ProductFlowRules

namespace APL.ProductFlow
open ProductLogic
open FlatProducts.LoopVerification

def logicalOp (isAnd : Bool) : BOp := if isAnd then .and else .or

theorem logical_short (hs : FlatProducts.shortCircuit (logicalOp isAnd) (.scalar (.bool value)) = true) :
    value = !isAnd := by cases isAnd <;> cases value <;> simp_all [logicalOp, FlatProducts.shortCircuit, APL.shortCircuit]

theorem logical_execute (hs : FlatProducts.shortCircuit (logicalOp isAnd) (.scalar (.bool value)) = false) :
    value = isAnd := by cases isAnd <;> cases value <;> simp_all [logicalOp, FlatProducts.shortCircuit, APL.shortCircuit]

theorem logical_apply : FlatProducts.binary (logicalOp isAnd) (.scalar (.bool isAnd)) (.scalar (.bool value)) =
    .value (.scalar (.bool value)) := by cases isAnd <;> cases value <;> rfl

theorem logical_binary_analysis_sound
    (wf : FlatProducts.WellTyped fs)
    (htl : FlatProducts.HasType (FlatProducts.signatures fs) context left (.scalar .bool))
    (htr : FlatProducts.HasType (FlatProducts.signatures fs) context right (.scalar .bool))
    (ls : SoundAt fs left context symbols path start first)
    (ln : start ≤ first.next) (lb : first.Bounded)
    (hb : asBoolean first.value = some test)
    (rs : SoundAt fs right context first.env
      (.and first.normal (if isAnd then .holds test else .holds (.unary .not test))) first.next second)
    (hg : (if isAnd then
      mergeFlow test second (single first.value first.env
        (.and first.normal (.holds (.unary .not test))) second.next)
      else mergeFlow test (single first.value first.env (.and first.normal (.holds test)) second.next) second) = some output) :
    SoundAt fs (.binary (logicalOp isAnd) left right) context symbols path start (sequence first output) := by
  intro model env he hen hp valid
  have firstValid : ValidFrom start model first.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ hc)
  have outputValid : ValidFrom start model output.checks :=
    valid_subset valid (fun _ hc => List.mem_append_right _ hc)
  have secondValid : ValidFrom start model second.checks := by
    apply valid_subset outputValid
    intro check hc
    cases isAnd with
    | true => rw [merge_flow_checks hg]; exact List.mem_append_left _ hc
    | false => rw [merge_flow_checks hg]; exact List.mem_append_right _ hc
  have testBound := as_boolean_supported hb lb.1
  apply binary_rule (spec_frame (ls model env he hen hp firstValid) wf htl hen)
  · intro value current hout hshort
    obtain ⟨⟨middle, ha, hp, hv, he⟩, _, _, _⟩ := hout
    obtain ⟨selected, rfl, htest⟩ := as_boolean_sound hb hv
    have hselected := logical_short hshort
    subst selected
    change Covered start model output (.scalar (.bool (!isAnd))) current
    apply covered_extend (ha := ha) (hn := ln)
    cases isAnd with
    | true =>
      apply merge_flow_covered hg htest testBound
      exact ⟨middle, agree_refl, ⟨hp, false_guard htest⟩, hv, he⟩
    | false =>
      apply merge_flow_covered hg htest testBound
      exact ⟨middle, agree_refl, ⟨hp, htest⟩, hv, he⟩
  · intro value current hout hshort
    obtain ⟨⟨middle, ha, hp, hv, he⟩, _, htyped, _⟩ := hout
    obtain ⟨selected, rfl, htest⟩ := as_boolean_sound hb hv
    have hselected := logical_execute hshort
    subst selected
    have execute : (if isAnd then Formula.holds test else .holds (.unary .not test)).Holds middle := by
      cases isAnd with
      | true => exact htest
      | false => exact false_guard htest
    apply spec_mono (spec_frame
      (rs middle current he htyped ⟨hp, execute⟩ (valid_extend secondValid ha ln)) wf htr htyped)
    intro other final hout
    obtain ⟨covered, _, _, htype⟩ := hout
    obtain ⟨scalar, rfl, hscalar⟩ := FlatProducts.scalar_canonical htype
    cases scalar with
    | int _ | unit => cases hscalar
    | bool value =>
      refine ⟨.scalar (.bool value), logical_apply, ?_⟩
      change Covered start model output (.scalar (.bool value)) final
      apply covered_extend (ha := ha) (hn := ln)
      cases isAnd with
      | true => exact merge_flow_covered hg htest testBound covered
      | false => exact merge_flow_covered hg htest testBound covered

end APL.ProductFlow
