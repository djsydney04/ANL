import ANL.BootSummaryCombinators
import ANL.BootSummaryDataBounds

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem episode_spec (value : Episode) :
    Spec (ascii (Output.episodeName value)) (toJson (Output.episodeName value)) 18 := by
  apply (Spec.ascii (episode_safe value)).mono
  have bounded := episode_bytes value
  omega
 theorem stack_spec (value : StackRole) :
    Spec (ascii (Output.stackName value)) (toJson (Output.stackName value)) 10 := by
  apply (Spec.ascii (stack_safe value)).mono
  have bounded := stack_bytes value
  omega
 theorem action_spec (value : ActionKind) :
    Spec (ascii (Output.actionName value)) (toJson (Output.actionName value)) 10 := by
  apply (Spec.ascii (action_safe value)).mono
  have bounded := action_bytes value
  omega
 theorem delivery_state_spec (value : DeliveryView) :
    Spec (ascii (Output.deliveryName value)) (toJson (Output.deliveryName value)) 9 := by
  apply (Spec.ascii (delivery_safe value)).mono
  have bounded := delivery_bytes value
  omega
 theorem status_spec (value : Status) : Spec (ascii value.name) (toJson value.name) 21 := by
  apply (Spec.ascii (status_safe value)).mono
  have bounded := status_bytes value
  omega

 theorem optional_spec (encode : α → Json) (value : Option α)
    (good : ∀ item, value = some item → Spec (write item) (encode item) bound)
    (nullBound : 4 ≤ bound) :
    Spec (optional write value) (Output.optionalJson encode value) bound := by
  cases value with
  | none => exact Spec.null.mono nullBound
  | some item => exact good item rfl

 theorem toJson_map_values [ToJson α] (values : List α) :
    toJson (values.map toJson) = toJson values := by
  change Json.arr ((values.map toJson).toArray.map id) = Json.arr (values.toArray.map toJson)
  simp

 theorem natural_array_spec (values : List Nat) (good : ∀ n ∈ values, n < 256) :
    Spec (array natural values) (toJson values) (2 + values.length * 4) := by
  simpa only [toJson_map_values] using
    Spec.array natural (fun n : Nat => toJson n) values (fun n member => Spec.natural_byte (good n member))

end ANL.Boot.Reference.Summary
