import ANL.WordsSimulationInitial

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

private theorem bind_parameters_total {params : List Mir.Temp} {values : List Val} (arity : values.length = params.length) :
    ∃ entries, Mir.bindParameters params values = some entries := by
  induction params generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨[], rfl⟩
      | cons value values => simp at arity
  | cons param params ih =>
      cases values with
      | nil => simp at arity
      | cons value values =>
          obtain ⟨entries, bound⟩ := ih (by simpa using arity)
          exact ⟨(param.id, value) :: entries, by simp [Mir.bindParameters, bound]⟩

private theorem bind_parameters_keys {params : List Mir.Temp} {values : List Val} {entries : Mir.Values} (bound : Mir.bindParameters params values = some entries) :
    entries.map Prod.fst = params.map Mir.Temp.id := by
  induction params generalizing values entries with
  | nil =>
      cases values <;> simp [Mir.bindParameters] at bound
      cases bound; rfl
  | cons param params ih =>
      cases values with
      | nil => simp [Mir.bindParameters] at bound
      | cons value values =>
          simp only [Mir.bindParameters, Option.map_eq_some_iff] at bound
          obtain ⟨rest, bound, rfl⟩ := bound
          simp [ih bound]

private theorem bind_parameters_lookup {params : List Mir.Temp} {values : List Val} {entries : Mir.Values}
    {index : Nat} {param : Mir.Temp} {value : Val} (bound : Mir.bindParameters params values = some entries)
    (unique : (params.map Mir.Temp.id).Nodup)
    (hp : params[index]? = some param) (hv : values[index]? = some value) :
    Mir.lookupId param.id entries = some value := by
  induction params generalizing index values entries with
  | nil => simp at hp
  | cons head params ih =>
      cases values with
      | nil => simp at hv
      | cons first values =>
          simp only [Mir.bindParameters, Option.map_eq_some_iff] at bound
          obtain ⟨rest, bound, rfl⟩ := bound
          have hn := List.nodup_cons.mp unique
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hv
              cases hp; cases hv
              simp [Mir.lookupId, ANL.Memory.Mir.lookupId]
          | succ index =>
              have hp' : params[index]? = some param := by simpa using hp
              have hv' : values[index]? = some value := by simpa using hv
              have ne : param.id ≠ head.id := by
                intro eq
                apply hn.1
                rw [← eq]
                exact List.mem_map.mpr ⟨param, List.mem_of_getElem? hp', rfl⟩
              simpa [Mir.lookupId, ANL.Memory.Mir.lookupId, ne] using ih bound hn.2 hp' hv'

private theorem locals_from_lookup {params : List Mir.Temp} {values : List Val} {target : Mir.Activation} (arity : values.length = params.length)
    (lookups : ∀ (index : Nat) (param : Mir.Temp) (value : Val), params[index]? = some param → values[index]? = some value →
      target.temp param = some value) :
    LocalsRel target (params.map Local.value) values := by
  induction params generalizing values with
  | nil => cases values with
      | nil => exact .nil
      | cons value values => simp at arity
  | cons param params ih =>
      cases values with
      | nil => simp at arity
      | cons value values =>
          exact .cons (lookups 0 param value rfl rfl)
            (ih (by simpa using arity) (fun index param value hp hv => lookups (index+1) param value hp hv))

private theorem locals_append (left : LocalsRel target ls vs) (right : LocalsRel target rs ws) :
    LocalsRel target (ls ++ rs) (vs ++ ws) := by
  induction left with
  | nil => exact right
  | cons hv _ ih => exact .cons hv ih

private theorem locals_reverse (h : LocalsRel target ls vs) :
    LocalsRel target ls.reverse vs.reverse := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => simpa only [List.reverse_cons] using locals_append ih (.cons hv .nil)

private theorem parameters_mutable_ids (params : List Mir.Temp) :
    mutableIds (params.map Local.value) = [] := by
  induction params with
  | nil => rfl
  | cons param params ih => exact ih

private def incoming_ids : Option ViewMode → List Nat
  | none => []
  | some _ => [0]

private theorem bind_view_related {view : Option ViewMode} {sourceLoan : Option ANL.Memory.Loan} (mode : view = ANL.Memory.loanMode sourceLoan) :
    ∃ resources, Mir.bindView (view.map (·, 0)) (sourceLoan.map loan) = some resources ∧
      ResourcesRel (incoming_ids view)
        (loanResources sourceLoan) resources := by
  subst view
  cases sourceLoan with
  | none => exact ⟨[], rfl, .nil⟩
  | some sourceLoan =>
      exact ⟨[(0, binding sourceLoan.binding)], by simp [ANL.Memory.loanMode, Mir.bindView, loan, binding_loan], .cons .nil⟩

theorem canonical_callee_related
    (lowered : Lowering.function fn = some mf)
    (arity : reversed.length = fn.params.length)
    (mode : fn.view = ANL.Memory.loanMode sourceLoan) :
    ∃ target, Mir.callee functionId mf (sourceLoan.map loan) reversed.reverse = some target ∧
      ActivationRel ((parameters fn.params).reverse.map Local.value)
        (match fn.view with | none => [] | some _ => [0])
        ⟨functionId, reversed, loanResources sourceLoan⟩ target ∧
      Below ⟨(parameters fn.params).length, 0⟩ target := by
  have metadata := function_metadata lowered
  have count : reversed.reverse.length = (parameters fn.params).length := by
    simpa [InventoryProof.parameters_length] using arity
  obtain ⟨temps, bound⟩ := bind_parameters_total count
  obtain ⟨resources, viewBound, resourceRel⟩ := bind_view_related mode
  let target : Mir.Activation := ⟨functionId, temps, [], resources⟩
  refine ⟨target, ?_, ?_, ?_⟩
  · simp only [Mir.callee, metadata.2.2.1, metadata.2.2.2.1, bound, viewBound,
      bind, Option.bind_some, pure, target]
  · have unique : ((parameters fn.params).map Mir.Temp.id).Nodup := by
      rw [InventoryProof.parameters_ids]
      exact List.nodup_range
    have forward : LocalsRel target ((parameters fn.params).map Local.value) reversed.reverse :=
      locals_from_lookup count (fun index param value hp hv => bind_parameters_lookup bound unique hp hv)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.reverse_reverse, List.map_reverse] using locals_reverse forward
    · rw [parameters_mutable_ids]; exact List.nodup_nil
    · exact (parameters_mutable_ids _).symm
    · exact resourceRel
    · cases fn.view <;> simp
  · refine ⟨?_, by simp [target]⟩
    intro key value membership
    have keymem : key ∈ (parameters fn.params).map Mir.Temp.id := by
      rw [← bind_parameters_keys bound]
      exact List.mem_map.mpr ⟨(key, value), membership, rfl⟩
    rw [InventoryProof.parameters_ids] at keymem
    simpa only [InventoryProof.parameters_length] using List.mem_range.mp keymem

end ANL.Words.Simulation
