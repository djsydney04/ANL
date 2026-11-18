import ANL.BootSummaryReadyProofs

namespace ANL.Boot.Reference.Summary
open ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem episode_safe (value : Episode) : SafeASCII (Output.episodeName value) := by
  cases value <;> unfold SafeASCII <;> decide
 theorem episode_bytes (value : Episode) : (Output.episodeName value).toUTF8.size ≤ 16 := by
  cases value <;> decide
 theorem stack_safe (value : StackRole) : SafeASCII (Output.stackName value) := by
  cases value <;> unfold SafeASCII <;> decide
 theorem stack_bytes (value : StackRole) : (Output.stackName value).toUTF8.size ≤ 8 := by
  cases value <;> decide
 theorem action_safe (value : ActionKind) : SafeASCII (Output.actionName value) := by
  cases value <;> unfold SafeASCII <;> decide
 theorem action_bytes (value : ActionKind) : (Output.actionName value).toUTF8.size ≤ 8 := by
  cases value <;> decide
 theorem delivery_safe (value : DeliveryView) : SafeASCII (Output.deliveryName value) := by
  cases value <;> unfold SafeASCII <;> decide
 theorem delivery_bytes (value : DeliveryView) : (Output.deliveryName value).toUTF8.size ≤ 7 := by
  cases value <;> decide
 theorem status_safe (value : Status) : SafeASCII value.name := by
  cases value <;> unfold SafeASCII <;> decide
 theorem status_bytes (value : Status) : value.name.toUTF8.size ≤ 19 := by
  cases value <;> decide

 theorem arguments_length (bounded : ArgumentsEncodable op args) : args.length ≤ 1 := by
  have length := bounded.1
  cases op <;> simp only [Operation.params] at length <;> simp only [List.length_cons, List.length_nil] at length <;> omega

 theorem arguments_values (bounded : ArgumentsEncodable op args) : ∀ item ∈ args, ValueEncodable item := by
  intro item present
  have byte := bounded.2 item present
  cases item with
  | unit => exact False.elim byte
  | byte n => exact byte

 theorem result_value (bounded : ResultEncodable op item) : ValueEncodable item := by
  cases op <;> cases item <;> simp_all [ResultEncodable, ValueEncodable]

 theorem origin_function_max (bounded : OriginEncodable loc) : loc.function ≤ 18446744073709551615 := by
  have bound := bounded.1
  change loc.function < 128 at bound
  omega

 theorem handler_function_max (context : ContextEncodable p) : p.entries.hardware.function ≤ 18446744073709551615 := by
  have bound := context.hardware
  change p.entries.hardware.function < 128 at bound
  omega

 theorem declaration_max (bound : ident < declarationLimit) : ident ≤ 18446744073709551615 := by
  change ident < 128 at bound
  omega

 theorem transition_max (bound : n ≤ transitionLimit + 1) : n ≤ 18446744073709551615 := by
  change n ≤ 65536 + 1 at bound
  omega

 theorem word_max (bound : n < wordModulus) : n ≤ 18446744073709551615 := by
  change n < 18446744073709551616 at bound
  omega

end ANL.Boot.Reference.Summary
