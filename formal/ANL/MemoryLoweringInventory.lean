import ANL.MemoryLowering

namespace ANL.Memory.Lowering

namespace InventoryProof

inductive Kind where
  | temp | slot | resource
  deriving DecidableEq

def ids (kind : Kind) (inventory : Mir.Inventory) : List Nat :=
  match kind with
  | .temp => inventory.temps
  | .slot => inventory.slots
  | .resource => inventory.resources

def hit (actual expected : Nat) : Nat := if actual = expected then 1 else 0

mutual
  def blockCount (kind : Kind) (id : Nat) : Mir.Block → Nat
    | .yield _ => 0
    | .next destination operation rest =>
        (if kind = .temp then hit destination.id id else 0) +
          operationCount kind id operation + blockCount kind id rest
  def operationCount (kind : Kind) (id : Nat) : Mir.Operation → Nat
    | .mutableScope slot _ body =>
        (if kind = .slot then hit slot.id id else 0) + blockCount kind id body
    | .whileE condition body => blockCount kind id condition + blockCount kind id body
    | .branch _ yes no => blockCount kind id yes + blockCount kind id no
    | .heapScope _ owner _ initial success failure =>
        (if kind = .resource then hit owner id else 0) + blockCount kind id initial +
          blockCount kind id success + blockCount kind id failure
    | .bufferWrite _ _ value => blockCount kind id value
    | _ => 0
end

def instructionCount (kind : Kind) (id : Nat) : List Mir.Instruction → Nat
  | [] => 0
  | i :: rest => (if kind = .temp then hit i.destination.id id else 0) +
      operationCount kind id i.operation + instructionCount kind id rest

theorem count_cons (id head : Nat) (tail : List Nat) :
    (head :: tail).count id = hit head id + tail.count id := by
  simp [List.count_cons, hit, Nat.add_comm]

theorem block_collect_count (b : Mir.Block) (kind : Kind) (id : Nat) (acc : Mir.Inventory) :
    (ids kind (b.collect acc)).count id = blockCount kind id b + (ids kind acc).count id := by
  induction b using Mir.Block.rec
    (motive_2 := fun op => ∀ kind id acc,
      (ids kind (op.collect acc)).count id = operationCount kind id op + (ids kind acc).count id)
    generalizing kind id acc <;>
    intros <;> simp_all [Mir.Block.collect, Mir.Operation.collect, blockCount, operationCount] <;>
    cases ‹Kind› <;> simp [ids, count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem instructions_count_block (instructions : List Mir.Instruction) (value : Mir.Temp)
    (kind : Kind) (id : Nat) :
    blockCount kind id (Mir.Block.fromInstructions instructions value) =
      instructionCount kind id instructions := by
  induction instructions with
  | nil => rfl
  | cons i rest ih =>
      simpa only [Mir.Block.fromInstructions, List.foldr_cons, blockCount, instructionCount,
        Nat.add_left_cancel_iff] using ih

theorem instructionCount_append (a b : List Mir.Instruction) (kind : Kind) (id : Nat) :
    instructionCount kind id (a ++ b) = instructionCount kind id a + instructionCount kind id b := by
  induction a <;> simp_all [instructionCount, Nat.add_assoc]

theorem fragment_block_count (f : Fragment) (kind : Kind) (id : Nat) :
    blockCount kind id f.block = instructionCount kind id f.instructions :=
  instructions_count_block ..

theorem emit_count (ty : Ty) (op : Mir.Operation) (before : List Mir.Instruction)
    (s : Supply) (kind : Kind) (id : Nat) :
    instructionCount kind id (emit ty op before s).1.instructions =
      instructionCount kind id before + (if kind = .temp then hit s.nextTemp id else 0) +
        operationCount kind id op := by
  simp [emit, instructionCount_append, instructionCount, Nat.add_assoc]

theorem range_count_succ (id n : Nat) :
    (List.range (n + 1)).count id = (List.range n).count id + hit n id := by
  simp [List.range_succ, count_cons]

structure Effect (offset : Nat) (sites : List Nat) (instructions : List Mir.Instruction)
    (before after : Supply) : Prop where
  temps : ∀ id, instructionCount .temp id instructions + (List.range before.nextTemp).count id =
    (List.range after.nextTemp).count id
  slots : ∀ id, instructionCount .slot id instructions + (List.range before.nextSlot).count id =
    (List.range after.nextSlot).count id
  resources : ∀ id, instructionCount .resource id instructions = (sites.map (· + offset)).count id

set_option linter.unusedSimpArgs false in
theorem term_effect (e : Term) (offset : Nat) (locals : Locals) (resources : List Nat)
    (before after : Supply) (f : Fragment)
    (lowered : term offset locals resources e before = some (f, after)) :
    Effect offset e.heapSites f.instructions before after := by
  induction e using Term.rec
    (motive_2 := fun args => ∀ offset locals resources before after (out : Arguments),
      arguments offset locals resources args before = some (out, after) →
        Effect offset (args.flatMap Term.heapSites) out.instructions before after)
    generalizing offset locals resources before after f with
  | lit ty value =>
      cases value <;> simp only [term, Option.some.injEq] at lowered <;> cases lowered
      all_goals
        refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | «local» ty index =>
      simp only [term, bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨binding, _, lowered⟩ := lowered
      cases binding <;> simp only [Option.pure_def, Option.some.injEq] at lowered <;> cases lowered
      all_goals
        refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | letE ty value body iv ib =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨initial, s1⟩, hi, ⟨result, s2⟩, hr, lowered⟩ := lowered
      cases lowered
      have ei := iv _ _ _ _ _ _ hi
      have er := ib _ _ _ _ _ _ hr
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ei_temps := ei.temps id
        have ei_slots := ei.slots id
        have ei_resources := ei.resources id
        have er_temps := er.temps id
        have er_slots := er.slots id
        have er_resources := er.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | letMut ty value body iv ib =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨initial, s1⟩, hi, ⟨result, s2⟩, hr, lowered⟩ := lowered
      cases lowered
      have ei := iv _ _ _ _ _ _ hi
      have er := ib _ _ _ _ _ _ hr
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ei_temps := ei.temps id
        have ei_slots := ei.slots id
        have ei_resources := ei.resources id
        have er_temps := er.temps id
        have er_slots := er.slots id
        have er_resources := er.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | assign ty index value iv =>
      simp only [term, bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨binding, _, lowered⟩ := lowered
      cases binding with
      | value temp => contradiction
      | mutable slot =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at lowered
        obtain ⟨⟨value, s1⟩, hv, lowered⟩ := lowered
        cases lowered
        have ev := iv _ _ _ _ _ _ hv
        refine ⟨?_, ?_, ?_⟩ <;> intro id
        all_goals
          have ev_temps := ev.temps id
          have ev_slots := ev.slots id
          have ev_resources := ev.resources id
          simp only [emit_count, fragment_block_count, instructionCount_append,
            operationCount, instructionCount, blockCount, Fragment.prefix, emit,
            Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
            List.count_append, List.count_nil, count_cons, range_count_succ,
            Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | whileE ty condition body ic ib =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fc, s1⟩, hc, ⟨fb, s2⟩, hb, lowered⟩ := lowered
      cases lowered
      have ec := ic _ _ _ _ _ _ hc
      have eb := ib _ _ _ _ _ _ hb
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ec_temps := ec.temps id
        have ec_slots := ec.slots id
        have ec_resources := ec.resources id
        have eb_temps := eb.temps id
        have eb_slots := eb.slots id
        have eb_resources := eb.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | ifE ty condition yes no ic iy ino =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fc, s1⟩, hc, ⟨fy, s2⟩, hy, ⟨fn, s3⟩, hn, lowered⟩ := lowered
      cases lowered
      have ec := ic _ _ _ _ _ _ hc
      have ey := iy _ _ _ _ _ _ hy
      have en := ino _ _ _ _ _ _ hn
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ec_temps := ec.temps id
        have ec_slots := ec.slots id
        have ec_resources := ec.resources id
        have ey_temps := ey.temps id
        have ey_slots := ey.slots id
        have ey_resources := ey.resources id
        have en_temps := en.temps id
        have en_slots := en.slots id
        have en_resources := en.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | unary ty op operand io =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fo, s1⟩, ho, lowered⟩ := lowered
      cases lowered
      have eo := io _ _ _ _ _ _ ho
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have eo_temps := eo.temps id
        have eo_slots := eo.slots id
        have eo_resources := eo.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | call ty fn args ia =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fa, s1⟩, ha, lowered⟩ := lowered
      cases lowered
      have ea := ia _ _ _ _ _ _ ha
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ea_temps := ea.temps id
        have ea_slots := ea.slots id
        have ea_resources := ea.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | tuple ty fields ia =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fa, s1⟩, ha, lowered⟩ := lowered
      cases lowered
      have ea := ia _ _ _ _ _ _ ha
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ea_temps := ea.temps id
        have ea_slots := ea.slots id
        have ea_resources := ea.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | project ty value index iv =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fv, s1⟩, hv, lowered⟩ := lowered
      cases lowered
      have ev := iv _ _ _ _ _ _ hv
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ev_temps := ev.temps id
        have ev_slots := ev.slots id
        have ev_resources := ev.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | heap ty site length initial success failure il ii isu ifa =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fl, s1⟩, hl, ⟨fi, s2⟩, hi, ⟨fsu, s3⟩, hsu, ⟨ffa, s4⟩, hfa, lowered⟩ := lowered
      cases lowered
      have el := il _ _ _ _ _ _ hl
      have ei := ii _ _ _ _ _ _ hi
      have esu := isu _ _ _ _ _ _ hsu
      have efa := ifa _ _ _ _ _ _ hfa
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have el_temps := el.temps id
        have el_slots := el.slots id
        have el_resources := el.resources id
        have ei_temps := ei.temps id
        have ei_slots := ei.slots id
        have ei_resources := ei.resources id
        have esu_temps := esu.temps id
        have esu_slots := esu.slots id
        have esu_resources := esu.resources id
        have efa_temps := efa.temps id
        have efa_slots := efa.slots id
        have efa_resources := efa.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | binary ty op left right il ir =>
      simp only [term, bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨⟨fl, s1⟩, hl, lowered⟩ := lowered
      have el := il _ _ _ _ _ _ hl
      split at lowered
      next _ =>
        simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
        obtain ⟨⟨fr, s2⟩, hr, lowered⟩ := lowered
        have er := ir _ _ _ _ _ _ hr
        split at lowered <;> cases lowered
        all_goals
          refine ⟨?_, ?_, ?_⟩ <;> intro id
        all_goals
          have el_temps := el.temps id
          have el_slots := el.slots id
          have el_resources := el.resources id
          have er_temps := er.temps id
          have er_slots := er.slots id
          have er_resources := er.resources id
          simp only [emit_count, fragment_block_count, instructionCount_append,
            operationCount, instructionCount, blockCount, Fragment.prefix, emit,
            Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
            List.count_append, List.count_nil, count_cons, range_count_succ,
            Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
      next _ =>
        simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
        obtain ⟨⟨fr, s2⟩, hr, lowered⟩ := lowered
        cases lowered
        have er := ir _ _ _ _ _ _ hr
        refine ⟨?_, ?_, ?_⟩ <;> intro id
        all_goals
          have el_temps := el.temps id
          have el_slots := el.slots id
          have el_resources := el.resources id
          have er_temps := er.temps id
          have er_slots := er.slots id
          have er_resources := er.resources id
          simp only [emit_count, fragment_block_count, instructionCount_append,
            operationCount, instructionCount, blockCount, Fragment.prefix, emit,
            Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
            List.count_append, List.count_nil, count_cons, range_count_succ,
            Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | bufferLength ty resource =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨resource, _, lowered⟩ := lowered
      cases lowered
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | bufferRead ty resource index ii =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨resource, _, ⟨fi, s1⟩, hi, lowered⟩ := lowered
      cases lowered
      have ei := ii _ _ _ _ _ _ hi
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ei_temps := ei.temps id
        have ei_slots := ei.slots id
        have ei_resources := ei.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | bufferWrite ty resource index value ii iv =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨resource, _, ⟨fi, s1⟩, hi, ⟨fv, s2⟩, hv, lowered⟩ := lowered
      cases lowered
      have ei := ii _ _ _ _ _ _ hi
      have ev := iv _ _ _ _ _ _ hv
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ei_temps := ei.temps id
        have ei_slots := ei.slots id
        have ei_resources := ei.resources id
        have ev_temps := ev.temps id
        have ev_slots := ev.slots id
        have ev_resources := ev.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | callView ty fn resource mode args ia =>
      simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨resource, _, ⟨fa, s1⟩, ha, lowered⟩ := lowered
      cases lowered
      have ea := ia _ _ _ _ _ _ ha
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have ea_temps := ea.temps id
        have ea_slots := ea.slots id
        have ea_resources := ea.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | nil =>
      rename_i offset locals resources before after out lowered
      simp only [arguments, Option.some.injEq] at lowered
      cases lowered
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega
  | cons head tail ih it =>
      rename_i offset locals resources before after out lowered
      simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fh, s1⟩, hh, ⟨ft, s2⟩, ht, lowered⟩ := lowered
      cases lowered
      have eh := ih _ _ _ _ _ _ hh
      have et := it _ _ _ _ _ _ ht
      refine ⟨?_, ?_, ?_⟩ <;> intro id
      all_goals
        have eh_temps := eh.temps id
        have eh_slots := eh.slots id
        have eh_resources := eh.resources id
        have et_temps := et.temps id
        have et_slots := et.slots id
        have et_resources := et.resources id
        simp only [emit_count, fragment_block_count, instructionCount_append,
          operationCount, instructionCount, blockCount, Fragment.prefix, emit,
          Term.heapSites, List.flatMap_nil, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.count_append, List.count_nil, count_cons, range_count_succ,
          Nat.zero_add, Nat.add_zero, ite_true, ite_false, reduceCtorEq] at * <;> omega

theorem parameters_ids (types : List Ty) :
    (parameters types).map Mir.Temp.id = List.range types.length := by
  simpa only [parameters, List.map_map, Function.comp_def, ← List.range_eq_range'] using
    List.zipIdx_map_snd 0 types

theorem parameters_length (types : List Ty) : (parameters types).length = types.length := by
  simp [parameters]

theorem resourceCount_range (offset n : Nat) : resourceCount offset (List.range n) = offset + n := by
  induction n with
  | zero => simp [resourceCount]
  | succ n ih =>
      rw [List.range_succ]
      unfold resourceCount at *
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih]
      omega

theorem resources_dense_count (view : Option ViewMode) (sites : List Nat)
    (canonical : sites = List.range sites.length) (id : Nat) :
    (sites.map (· + viewOffset view)).count id +
      (match view with | none => [] | some _ => [0]).count id =
        (List.range (resourceCount (viewOffset view) sites)).count id := by
  rw [canonical]
  simp only [resourceCount_range]
  cases view with
  | none => simp [viewOffset]
  | some mode =>
      simp only [viewOffset, Option.isSome_some, ite_true, Nat.add_comm 1]
      rw [List.range_succ_eq_map]
      simp only [count_cons, List.count_nil, Nat.add_zero]
      change _ + _ = hit 0 id + (List.map (fun x => x + 1) (List.range sites.length)).count id
      omega

end InventoryProof

open InventoryProof in
theorem function_tables
    {fn : ANL.Memory.Function} {out : ANL.Memory.Mir.Function}
    (sites : fn.body.CanonicalSites)
    (lowered : function fn = some out) :
    ANL.Memory.Mir.Dense out.inventory.temps out.tempCount ∧
    ANL.Memory.Mir.Dense out.inventory.slots out.slotCount ∧
    ANL.Memory.Mir.Dense out.inventory.resources out.resourceCount := by
  simp only [function, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨body, supply⟩, bodyLowered, lowered⟩ := lowered
  cases lowered
  have effect := term_effect _ _ _ _ _ _ _ bodyLowered
  refine ⟨List.perm_iff_count.mpr ?_, List.perm_iff_count.mpr ?_, List.perm_iff_count.mpr ?_⟩
  · intro id
    have collect := block_collect_count body.block .temp id
      ⟨(parameters fn.params).map Mir.Temp.id, [], match fn.view with | none => [] | some _ => [0]⟩
    simp only [ids, fragment_block_count, parameters_ids] at collect
    have temps := effect.temps id
    simp only [parameters_length] at temps
    cases viewEq : fn.view <;>
      simpa only [Mir.Function.inventory, viewEq, Option.map_some, Option.map_none, parameters_ids]
        using collect.trans temps
  · intro id
    have collect := block_collect_count body.block .slot id
      ⟨(parameters fn.params).map Mir.Temp.id, [], match fn.view with | none => [] | some _ => [0]⟩
    simp only [ids, fragment_block_count] at collect
    cases viewEq : fn.view <;>
      simpa only [Mir.Function.inventory, viewEq, Option.map_some, Option.map_none, parameters_ids]
        using collect.trans (effect.slots id)
  · intro id
    have collect := block_collect_count body.block .resource id
      ⟨(parameters fn.params).map Mir.Temp.id, [], match fn.view with | none => [] | some _ => [0]⟩
    have resources := resources_dense_count fn.view fn.body.heapSites sites id
    simp only [fragment_block_count, effect.resources, ids] at collect
    cases viewEq : fn.view <;>
      simpa only [Mir.Function.inventory, viewEq, Option.map_some, Option.map_none, parameters_ids]
        using collect.trans resources

end ANL.Memory.Lowering
