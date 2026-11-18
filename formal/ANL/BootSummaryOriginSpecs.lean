import ANL.BootSummaryComponentSupport

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem edge_spec (bounded : EdgeEncodable item) : Spec (edge item) (Output.edgeJson item) 64 := by
  cases item with
  | letValue =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "letValue") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | letBody =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "letBody") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | whileCondition =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "whileCondition") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | whileBody =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "whileBody") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | ifCondition =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "ifCondition") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | ifThen =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "ifThen") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | ifElse =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "ifElse") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | unaryOperand =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "unaryOperand") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | binaryLeft =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "binaryLeft") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | binaryRight =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "binaryRight") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | callArgument index =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "callArgument") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "index") (by unfold SafeASCII; decide) (Spec.natural (n := index) (by exact bounded)) FieldSpec.nil rfl) rfl) (by change (["edge", "index"] : List String).Nodup; decide)).mono (by decide)
  | convertOperand =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "convertOperand") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | tupleField index =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "tupleField") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "index") (by unfold SafeASCII; decide) (Spec.natural (n := index) (by exact bounded)) FieldSpec.nil rfl) rfl) (by change (["edge", "index"] : List String).Nodup; decide)).mono (by decide)
  | projectOperand =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "projectOperand") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)
  | assignValue =>
    simp only [edge, Output.edgeJson]
    exact (Spec.object (FieldSpec.cons (key := "edge") (by unfold SafeASCII; decide) (Spec.ascii (value := "assignValue") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["edge"] : List String).Nodup; decide)).mono (by decide)

 theorem origin_spec (bounded : OriginEncodable loc) : Spec (origin loc) (Output.originJson loc) 8448 := by
  have path : Spec (array edge loc.path) (toJson (loc.path.map Output.edgeJson)) 8322 := by
    apply (Spec.array edge Output.edgeJson loc.path (fun e present => edge_spec (bounded.2.2 e present))).mono
    have length := bounded.2.1
    change loc.path.length ≤ 128 at length
    omega
  unfold origin Output.originJson
  exact (Spec.object (FieldSpec.cons (key := "function") (by unfold SafeASCII; decide) (Spec.natural (n := loc.function) (by exact origin_function_max bounded)) (FieldSpec.cons (key := "core_path") (by unfold SafeASCII; decide) path FieldSpec.nil rfl) rfl) (by change (["function", "core_path"] : List String).Nodup; decide)).mono (by decide)

 theorem operation_spec (context : ContextEncodable p) (valid : op.Valid p.entries.hardware.function) :
    Spec (operation op) (Output.operationJson op) 256 := by
  cases valid with
  | read8 =>
    simp only [operation, Output.operationJson]
    exact (Spec.object (FieldSpec.cons (key := "tag") (by unfold SafeASCII; decide) (Spec.ascii (value := "mmio_read8") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "region") (by unfold SafeASCII; decide) (Spec.natural (n := 0) (by decide)) (FieldSpec.cons (key := "offset") (by unfold SafeASCII; decide) (Spec.natural (n := 5) (by decide)) FieldSpec.nil rfl) rfl) rfl) (by change (["tag", "region", "offset"] : List String).Nodup; decide)).mono (by decide)
  | @write8 offset allowed =>
    have upper : offset ≤ 18446744073709551615 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
      omega
    simp only [operation, Output.operationJson]
    exact (Spec.object (FieldSpec.cons (key := "tag") (by unfold SafeASCII; decide) (Spec.ascii (value := "mmio_write8") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "region") (by unfold SafeASCII; decide) (Spec.natural (n := 0) (by decide)) (FieldSpec.cons (key := "offset") (by unfold SafeASCII; decide) (Spec.natural (n := offset) (by exact upper)) FieldSpec.nil rfl) rfl) rfl) (by change (["tag", "region", "offset"] : List String).Nodup; decide)).mono (by decide)
  | fence =>
    simp only [operation, Output.operationJson]
    exact (Spec.object (FieldSpec.cons (key := "tag") (by unfold SafeASCII; decide) (Spec.ascii (value := "io_fence") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "region") (by unfold SafeASCII; decide) (Spec.natural (n := 0) (by decide)) FieldSpec.nil rfl) rfl) (by change (["tag", "region"] : List String).Nodup; decide)).mono (by decide)
  | csrClear =>
    simp only [operation, Output.operationJson]
    exact (Spec.object (FieldSpec.cons (key := "tag") (by unfold SafeASCII; decide) (Spec.ascii (value := "csr_clear") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "authority") (by unfold SafeASCII; decide) (Spec.natural (n := 0) (by decide)) (FieldSpec.cons (key := "register") (by unfold SafeASCII; decide) (Spec.ascii (value := "sstatus") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "mask") (by unfold SafeASCII; decide) (Spec.word (n := 2) (by decide)) FieldSpec.nil rfl) rfl) rfl) rfl) (by change (["tag", "authority", "register", "mask"] : List String).Nodup; decide)).mono (by decide)
  | csrWrite =>
    simp only [operation, Output.operationJson]
    exact (Spec.object (FieldSpec.cons (key := "tag") (by unfold SafeASCII; decide) (Spec.ascii (value := "csr_write") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "authority") (by unfold SafeASCII; decide) (Spec.natural (n := 0) (by decide)) (FieldSpec.cons (key := "register") (by unfold SafeASCII; decide) (Spec.ascii (value := "sie") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "value") (by unfold SafeASCII; decide) (Spec.word (n := 0) (by decide)) FieldSpec.nil rfl) rfl) rfl) rfl) (by change (["tag", "authority", "register", "value"] : List String).Nodup; decide)).mono (by decide)
  | installTrap =>
    simp only [operation, Output.operationJson]
    exact (Spec.object (FieldSpec.cons (key := "tag") (by unfold SafeASCII; decide) (Spec.ascii (value := "install_trap") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "authority") (by unfold SafeASCII; decide) (Spec.natural (n := 0) (by decide)) (FieldSpec.cons (key := "handler") (by unfold SafeASCII; decide) (Spec.natural (n := p.entries.hardware.function) (by exact handler_function_max context)) FieldSpec.nil rfl) rfl) rfl) (by change (["tag", "authority", "handler"] : List String).Nodup; decide)).mono (by decide)

 theorem value_spec (bounded : ValueEncodable item) : Spec (value item) (Output.valueJson item) 64 := by
  cases item with
  | unit =>
    simp only [value, Output.valueJson]
    exact (Spec.object (FieldSpec.cons (key := "type") (by unfold SafeASCII; decide) (Spec.ascii (value := "unit") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["type"] : List String).Nodup; decide)).mono (by decide)
  | byte n =>
    simp only [value, Output.valueJson]
    exact (Spec.object (FieldSpec.cons (key := "type") (by unfold SafeASCII; decide) (Spec.ascii (value := "u8") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "value") (by unfold SafeASCII; decide) (Spec.natural_byte (n := n) bounded) FieldSpec.nil rfl) rfl) (by change (["type", "value"] : List String).Nodup; decide)).mono (by decide)

end ANL.Boot.Reference.Summary
