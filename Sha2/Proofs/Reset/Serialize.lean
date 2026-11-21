import Sha2.Proofs.Common.SHA256.Instances.Absorb.LoadPre
import Sha2.Proofs.Reset.Prefix
import Sha2.Proofs.Reset.Memory
import Sha2.Proofs.Common.SHA256.Instances.Digest.Serialize
import Sha2.Proofs.Common.SHA256.Instances.Finalize
import X86Proofs.Instructions.MovLoad.Triple
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Instances Sha2.Proofs.Common.Instructions

private theorem serialize_regions_avoid {routine : Routine} {initial : RamState} {inputs : Array Input}
    (call : TwoOutputs.ValidCall routine initial inputs) :
    ∀ region ∈ regions routine initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion routine initial,
      TwoOutputs.secondOutputRegion routine initial, Stack.region initial routine.minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

theorem serialize_load_generic [bindings : Bindings] (v : Wrapper.Variant)
    (routine : Routine) (frame : Nat) (offset : Serialize.HashOffset)
    (capacity : frame ≤ routine.minStackBytes) (fits : offset.value + 32 ≤ frame)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32} (pc : BitVec 64)
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - BitVec.ofNat 64 frame) (rip : s.RIP = pc)
    (words : HashStateAt s (rspOf s + BitVec.ofNat 64 offset.value) hash)
    (inside : BlockInProgram pc (Serialize.bytes (.loadSwap offset (v == .sha224))).length)
    (code : CodeIn (codeRange pc (Serialize.bytes (.loadSwap offset (v == .sha224)))) s) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      (Serialize.effect pc (.loadSwap offset (v == .sha224)) s).Holds s t ∧
      Serialize.SwappedRegisters t hash (v == .sha224) := by
  have read (offset len : Nat) (bound : offset + len ≤ frame) :
      MemReadable s (rspOf s + BitVec.ofNat 64 offset) len := by
    rw [rsp]
    exact stack_frame_readable call.stack (frame := frame) capacity state.allocated bound
  have pre : Serialize.LoadPre pc offset s (v == .sha224) :=
    ⟨rip, read (offset.value + 0) 4 (by omega), read (offset.value + 4) 4 (by omega),
      read (offset.value + 8) 4 (by omega), read (offset.value + 12) 4 (by omega),
      read (offset.value + 16) 4 (by omega), read (offset.value + 20) 4 (by omega),
      read (offset.value + 24) 4 (by omega), by cases v with
        | sha224 => trivial
        | sha256 => exact read (offset.value + 28) 4 (by omega)⟩
  obtain ⟨fuel, t, run, ready, _, result⟩ := Serialize.run pc (.loadSwap offset (v == .sha224))
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    inside s (supportedMachine_readyToStep state.machine) code pre
  refine ⟨t, state.of_agrees (serialize_regions_avoid call) run ready result.agrees ?_ ?_,
    result, Serialize.loadSwap_words pre words result⟩
  · intro c hc a ha
    have nomem : ∀ c ∈ (Serialize.effect pc (.loadSwap offset (v == .sha224)) s).components,
        ∀ a, ¬ c.Covers a := by
      cases v <;> simp [Serialize.effect, Effect.components, Component.Covers]
    exact (nomem c hc a ha).elim
  · cases v <;> simp [Serialize.effect, Effect.components]

theorem serialize_load [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32} (pc : BitVec 64)
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64) (rip : s.RIP = pc)
    (words : HashStateAt s (rspOf s + 64#64) hash)
    (inside : BlockInProgram pc (Serialize.bytes (.loadSwap .at64 (v == .sha224))).length)
    (code : CodeIn (codeRange pc (Serialize.bytes (.loadSwap .at64 (v == .sha224)))) s) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      (Serialize.effect pc (.loadSwap .at64 (v == .sha224)) s).Holds s t ∧
      Serialize.SwappedRegisters t hash (v == .sha224) := by
  exact serialize_load_generic v (resetRoutine v) 248 .at64
    (by rw [resetRoutine_stack]; decide) (by decide) pc machine call state rsp rip words inside code

theorem serialize_store_generic [bindings : Bindings] (v : Wrapper.Variant) (routine : Routine)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (pc : BitVec 64) (output : Serialize.OutputRegister) (destination : BitVec 64)
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (member : (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion routine initial,
        TwoOutputs.secondOutputRegion routine initial])
    (outputA : (.reg output.value : Operand 64).read s = destination)
    (words : Serialize.SwappedRegisters s hash (v == .sha224))
    (rip : s.RIP = pc)
    (inside : BlockInProgram pc (Serialize.bytes (.store output (v == .sha224))).length)
    (code : CodeIn (codeRange pc (Serialize.bytes (.store output (v == .sha224)))) s) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      (Serialize.effect pc (.store output (v == .sha224)) s).Holds s t ∧
      MemoryWriteFrame s t #v[(⟨destination.toNat, v.outputBytes⟩ : MemoryRegion)] ∧
      (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion).HasBytes t.external
        (if v == .sha224 then (serializeHash hash).extract 0 28 else serializeHash hash) := by
  have sizeEqual : (if v == .sha224 then 28 else 32) = v.outputBytes := by cases v <;> rfl
  have valid := call.outputInMemory _ member
  have outputContains {addr : BitVec 64}
      (covered : (Component.mem destination v.outputBytes).Covers addr) :
      (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion).Contains addr.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    exact memoryRegion_contains_add valid.2.1 (Nat.le_refl _) (Nat.le_refl _) hi
  have readable : MemReadable s destination v.outputBytes :=
    Common.Encoding.Serialize.readable_of_grow
      (memoryRegion_memReadable valid.2.1 valid.2.2 (Nat.le_refl _) (Nat.le_refl _)) state.allocated
  have outerMember : (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion routine initial,
        TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes] :=
    List.mem_append_left [Stack.region initial routine.minStackBytes] member
  have writable : CrossPageStore.Writable s destination v.outputBytes := by
    refine ⟨readable, tables_of_not_reserved (by cases v <;> decide) readable.low ?_⟩
    intro i hi reserved
    exact (call.separation.2 _ outerMember).2 _ (outputContains ⟨i, hi, rfl⟩) (.inr reserved)
  have apart : RangeApart destination v.outputBytes pc
      (Serialize.bytes (.store output (v == .sha224))).length := by
    intro i hi j hj equal
    apply (call.separation.2 _ outerMember).2 _ (outputContains ⟨i, hi, rfl⟩)
    left
    rw [equal]
    exact inside j (Nat.le_of_lt hj)
  have pre : Serialize.StorePre pc output s (v == .sha224) :=
    Instances.Digest.store_pre rip (outputA ▸ writable) (outputA ▸ apart)
  obtain ⟨fuelT, t, runT, readyT, _, store⟩ := Serialize.run pc (.store output (v == .sha224))
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    inside s (supportedMachine_readyToStep state.machine) code pre
  have contained (offset : Nat) (bound : offset + 4 ≤ v.outputBytes) {addr : BitVec 64}
      (covered : (Component.mem ((.reg output.value : Operand 64).read s + BitVec.ofNat 64 offset) 4).Covers addr) :
      (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion).Contains addr.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    rw [outputA, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact outputContains ⟨offset+i, by omega, rfl⟩
  have within : WritesWithin (Serialize.effect pc (.store output (v == .sha224)) s).components
      #v[(⟨destination.toNat, v.outputBytes⟩ : MemoryRegion)] := by
    intro comp hc addr ha
    refine ⟨(⟨destination.toNat, v.outputBytes⟩ : MemoryRegion), by simp, ?_⟩
    cases v <;> simp only [Serialize.effect, Effect.components,
      show (Wrapper.Variant.sha224 == .sha224) = true from by decide,
      show (Wrapper.Variant.sha256 == .sha224) = false from by decide,
      Bool.false_eq_true, ite_false, ite_true, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc
    all_goals try exact ha.elim
    all_goals try (rcases hc with rfl | rfl)
    all_goals try exact ha.elim
    all_goals first
      | exact contained 0 (by decide) ha
      | exact contained 4 (by decide) ha
      | exact contained 8 (by decide) ha
      | exact contained 12 (by decide) ha
      | exact contained 16 (by decide) ha
      | exact contained 20 (by decide) ha
      | exact contained 24 (by decide) ha
      | exact contained 28 (by decide) ha
  have stateT : ExecutionState initial t (regions routine initial) :=
    state.of_agrees (serialize_regions_avoid call) runT readyT store.agrees
      (by
        intro c hc a ha
        obtain ⟨region, hr, covered⟩ := within c hc a ha
        simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at hr
        subst region
        refine ⟨_, ?_, covered⟩
        simp only [regions, Vector.mem_mk, List.mem_toArray]
        exact List.mem_append_left [Stack.region initial routine.minStackBytes] member)
      (by cases v <;> simp [Serialize.effect, Effect.components])
  have payload := Serialize.store_hasBytes words store (fun i hi => by
    rw [outputA]
    exact store.agrees.grow _ (readable.mem i (by simpa only [sizeEqual] using hi)))
  rw [sizeEqual, outputA] at payload
  exact ⟨t, stateT, store, store.agrees.memoryWriteFrame within, payload⟩

theorem serialize_store [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (pc : BitVec 64) (output : Serialize.OutputRegister) (destination : BitVec 64)
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (member : (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion (resetRoutine v) initial,
        TwoOutputs.secondOutputRegion (resetRoutine v) initial])
    (outputA : (.reg output.value : Operand 64).read s = destination)
    (words : Serialize.SwappedRegisters s hash (v == .sha224))
    (rip : s.RIP = pc)
    (inside : BlockInProgram pc (Serialize.bytes (.store output (v == .sha224))).length)
    (code : CodeIn (codeRange pc (Serialize.bytes (.store output (v == .sha224)))) s) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      (Serialize.effect pc (.store output (v == .sha224)) s).Holds s t ∧
      MemoryWriteFrame s t #v[(⟨destination.toNat, v.outputBytes⟩ : MemoryRegion)] ∧
      (⟨destination.toNat, v.outputBytes⟩ : MemoryRegion).HasBytes t.external
        (if v == .sha224 then (serializeHash hash).extract 0 28 else serializeHash hash) := by
  exact serialize_store_generic v (resetRoutine v) pc output destination machine call state
    member outputA words rip inside code

theorem serialize_preserves_first {routine : Routine} {initial s t : RamState}
    {inputs : Array Input} {bytes : ByteArray}
    (call : TwoOutputs.ValidCall routine initial inputs)
    (written : (TwoOutputs.outputRegion routine initial).HasBytes s.external bytes)
    (frame : MemoryWriteFrame s t #v[TwoOutputs.secondOutputRegion routine initial]) :
    (TwoOutputs.outputRegion routine initial).HasBytes t.external bytes := by
  apply Common.Memory.hasBytes_of_frame written
    (call.outputInMemory _ (by simp)).2.1 frame
  intro region member
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at member
  subst region
  have pairs := call.separation.1
  simp only [List.pairwise_cons] at pairs
  exact pairs.1 _ (by simp)

theorem resetOutput_preserves_swapped {v : Wrapper.Variant} {s t : RamState}
    {base : BitVec 64} {hash : Array UInt32}
    (words : Serialize.SwappedRegisters s hash (v == .sha224))
    (result : Initialize.Post (Initialization.resetOutput.layout v) base s t) :
    Serialize.SwappedRegisters t hash (v == .sha224) := by
  refine ⟨words.1, fun j hj => ?_⟩
  rw [result.frame.read (n := 32) (r := Serialize.wordRegister j) ?_]
  · exact words.2 j hj
  · have bound : j < 8 := by split at hj <;> omega
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    all_goals cases v
    all_goals try (simp at hj)
    all_goals change Component.reg _ ∉ _
    all_goals simp [Initialize.Layout.components, Initialization.layout,
      Initialization.word, Initialization.temporary, Serialize.wordRegister]

def resetLoadPC (v : Wrapper.Variant) (last : Bool) : BitVec 64 :=
  ((if last then Finalization.resetLast else Finalization.resetFirst).layout v).exit

def resetStorePC (v : Wrapper.Variant) (last : Bool) : BitVec 64 :=
  if last then resetLoadPC v true +
    BitVec.ofNat 64 (Serialize.bytes (.loadSwap .at64 (v == .sha224))).length + 8#64
  else (Initialization.resetOutput.layout v).finish

theorem reset_load_code (v : Wrapper.Variant) (last : Bool) {s : RamState}
    (loaded : ProgramLoaded s) :
    CodeIn (codeRange (resetLoadPC v last) (Serialize.bytes (.loadSwap .at64 (v == .sha224)))) s := by
  have pc : resetLoadPC v last = Extracted.textAddress +
      BitVec.ofNat 64 ((resetLoadPC v last).toNat - 0x100000) := by
    cases v <;> cases last <;> decide +kernel
  rw [pc]
  apply programText_slice (programLoaded_codeIn loaded)
  · cases v <;> cases last <;> decide +kernel
  · cases v <;> cases last <;> decide +kernel

theorem reset_load_inside (v : Wrapper.Variant) (last : Bool) :
    BlockInProgram (resetLoadPC v last) (Serialize.bytes (.loadSwap .at64 (v == .sha224))).length := by
  have pc : resetLoadPC v last = Extracted.textAddress +
      BitVec.ofNat 64 ((resetLoadPC v last).toNat - 0x100000) := by
    cases v <;> cases last <;> decide +kernel
  rw [pc]
  apply blockInProgram_of_textOffset
  cases v <;> cases last <;> decide +kernel

theorem reset_load_first_next (v : Wrapper.Variant) :
    resetLoadPC v false + BitVec.ofNat 64 (Serialize.bytes (.loadSwap .at64 (v == .sha224))).length =
      (Initialization.resetOutput.layout v).start := by
  cases v <;> decide +kernel

theorem serialize_second_pointer_generic [bindings : Bindings] (v : Wrapper.Variant)
    (routine : Routine) (frame slot : Nat) (pc : BitVec 64)
    (capacity : frame ≤ routine.minStackBytes) (fits : slot + 8 ≤ frame)
    (slotLow : slot < 2^31)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - BitVec.ofNat 64 frame)
    (rip : s.RIP = pc)
    (saved : memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 = initial.regValue .r8)
    (words : Serialize.SwappedRegisters s hash (v == .sha224))
    (loaded : CodeIn (codeRange pc
      ([0x4c, 0x8b, if v = .sha224 then 0x94 else 0x9c, 0x24] ++
        immBytes 32 (BitVec.ofNat 32 slot))) s)
    (target : InProgram (pc + 8#64)) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      t.RIP = pc + 8#64 ∧
      (.reg (if v = .sha224 then 10 else 11) : Operand 64).read t = initial.regValue .r8 ∧
      Serialize.SwappedRegisters t hash (v == .sha224) ∧
      AgreesExcept [.reg (if v = .sha224 then 10 else 11), .rip] s t := by
  have readable : MemReadable s (rspOf s + BitVec.ofNat 64 slot) 8 := by
    rw [rsp]
    exact stack_frame_readable call.stack (frame := frame) capacity state.allocated fits
  have step := mov_r64_m64_effect_step pc 0x4c (by simp [RexWPrefix])
    (if v = .sha224 then 2 else 3) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 slot)))
    (by simp [AddrMode.Valid]) rfl rfl
  obtain ⟨t, run, ready, result⟩ := step.advances (boundary := returnBoundary initial) (supportedMachine_readyToStep state.machine)
    (by cases v <;> simpa [AddrMode.modrm, AddrMode.mod, AddrMode.rm, Disp.mod,
      AddrMode.tail, Disp.bytes, AddrMode.sibByte, idxLow, regLow] using loaded) ⟨rip, by
      change MemReadable s (rspOf s + (Disp.d32 (BitVec.ofNat 32 slot)).value) 8
      have address : (Disp.d32 (BitVec.ofNat 32 slot)).value = BitVec.ofNat 64 slot :=
        Absorption.d32_value_ofNat slot slotLow
      rw [address]
      exact readable⟩
    (by
      change pc + 8#64 ≠ (returnBoundary initial).rip
      exact boundary_ne_program (valid_return_boundary machine call.stack call.returnAddress).2.2 target)
  have frame : AgreesExcept [.reg (if v = .sha224 then 10 else 11), .rip] s t := by
    cases v <;> exact result.agrees
  have stateT : ExecutionState initial t (regions routine initial) :=
    state.of_agrees (serialize_regions_avoid call) run ready frame
      (by intro c hc a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> exact ha.elim)
      (by simp)
  refine ⟨t, stateT, ?_, ?_, ?_, frame⟩
  · exact result.rip
  · have value : (.reg (if v = .sha224 then 10 else 11) : Operand 64).read t =
        memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 := by
      have address : (Disp.d32 (BitVec.ofNat 32 slot)).value = BitVec.ofNat 64 slot :=
        Absorption.d32_value_ofNat slot slotLow
      rw [← address]
      cases v <;> exact result.writes
    exact value.trans saved
  · refine ⟨words.1, fun j hj => ?_⟩
    rw [frame.read (n := 32) (r := Serialize.wordRegister j) ?_]
    · exact words.2 j hj
    · have bound : j < 8 := by split at hj <;> omega
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      all_goals cases v
      all_goals try (simp at hj)
      all_goals decide +kernel

theorem serialize_second_pointer [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = resetStorePC v true - 8#64)
    (saved : memLoad s.external (rspOf s + 192#64) 64 = initial.regValue .r8)
    (words : Serialize.SwappedRegisters s hash (v == .sha224)) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      t.RIP = resetStorePC v true ∧
      (.reg (if v = .sha224 then 10 else 11) : Operand 64).read t = initial.regValue .r8 ∧
      Serialize.SwappedRegisters t hash (v == .sha224) ∧
      AgreesExcept [.reg (if v = .sha224 then 10 else 11), .rip] s t := by
  let pc := resetStorePC v true - 8#64
  have nextPC : pc + 8#64 = resetStorePC v true := by cases v <;> decide +kernel
  have loaded : CodeIn (codeRange pc
      [0x4c, 0x8b, if v = .sha224 then 0x94 else 0x9c, 0x24, 0xc0, 0, 0, 0]) s := by
    have eq : pc = Extracted.textAddress + BitVec.ofNat 64 (pc.toNat - 0x100000) := by
      cases v <;> decide +kernel
    rw [eq]
    apply programText_slice (programLoaded_codeIn state.loaded)
    · cases v <;> decide +kernel
    · cases v <;> decide +kernel
  have target : InProgram (resetStorePC v true) := by
    have eq : resetStorePC v true = Extracted.textAddress +
        BitVec.ofNat 64 ((resetStorePC v true).toNat - 0x100000) := by
      cases v <;> decide +kernel
    rw [eq]
    exact inProgram_of_textOffset _ (by cases v <;> decide +kernel)
  obtain ⟨t, stateT, ripT, output, swapped, frameT⟩ :=
    serialize_second_pointer_generic v (resetRoutine v) 248 192 pc
      (by rw [resetRoutine_stack]; decide) (by decide) (by decide)
      machine call state rsp rip saved words loaded (nextPC.symm ▸ target)
  exact ⟨t, stateT, ripT.trans nextPC, output, swapped, frameT⟩

theorem reset_store_code (v : Wrapper.Variant) (last : Bool) {s : RamState}
    (loaded : ProgramLoaded s) :
    CodeIn (codeRange (resetStorePC v last)
      (Serialize.bytes (.store (if last then (if v = .sha224 then .r10 else .r11) else .r13) (v == .sha224)))) s := by
  have pc : resetStorePC v last = Extracted.textAddress +
      BitVec.ofNat 64 ((resetStorePC v last).toNat - 0x100000) := by
    cases v <;> cases last <;> decide +kernel
  rw [pc]
  apply programText_slice (programLoaded_codeIn loaded)
  · cases v <;> cases last <;> decide +kernel
  · cases v <;> cases last <;> decide +kernel

theorem reset_store_inside (v : Wrapper.Variant) (last : Bool) :
    BlockInProgram (resetStorePC v last)
      (Serialize.bytes (.store (if last then (if v = .sha224 then .r10 else .r11) else .r13) (v == .sha224))).length := by
  have pc : resetStorePC v last = Extracted.textAddress +
      BitVec.ofNat 64 ((resetStorePC v last).toNat - 0x100000) := by
    cases v <;> cases last <;> decide +kernel
  rw [pc]
  apply blockInProgram_of_textOffset
  cases v <;> cases last <;> decide +kernel

theorem serialized_last_generic [bindings : Bindings] (v : Wrapper.Variant)
    (routine : Routine) (frame : Nat) (offset : Serialize.HashOffset) (slot : Nat)
    (loadPC storePC : BitVec 64)
    (capacity : frame ≤ routine.minStackBytes) (hashFits : offset.value + 32 ≤ frame)
    (slotFits : slot + 8 ≤ frame) (slotLow : slot < 2^31)
    (outputSize : routine.outputBytes = v.outputBytes)
    (nextPC : loadPC + BitVec.ofNat 64
      (Serialize.bytes (.loadSwap offset (v == .sha224))).length = storePC - 8#64)
    (loadInside : BlockInProgram loadPC
      (Serialize.bytes (.loadSwap offset (v == .sha224))).length)
    (loadCode : ∀ {s : RamState}, ProgramLoaded s →
      CodeIn (codeRange loadPC (Serialize.bytes (.loadSwap offset (v == .sha224)))) s)
    (pointerCode : ∀ {s : RamState}, ProgramLoaded s →
      CodeIn (codeRange (storePC - 8#64)
        ([0x4c, 0x8b, if v = .sha224 then 0x94 else 0x9c, 0x24] ++
          immBytes 32 (BitVec.ofNat 32 slot))) s)
    (target : InProgram storePC)
    (storeInside : BlockInProgram storePC
      (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224))).length)
    (storeCode : ∀ {s : RamState}, ProgramLoaded s →
      CodeIn (codeRange storePC
        (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224)))) s)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32} {first : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - BitVec.ofNat 64 frame)
    (rip : s.RIP = loadPC)
    (words : HashStateAt s (rspOf s + BitVec.ofNat 64 offset.value) hash)
    (saved : memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 = initial.regValue .r8)
    (firstBytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      t.RIP = storePC + BitVec.ofNat 64
        (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224))).length ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external first ∧
      (TwoOutputs.secondOutputRegion routine initial).HasBytes t.external
        (if v == .sha224 then (serializeHash hash).extract 0 28 else serializeHash hash) ∧
      rspOf t = rspOf s ∧
      MemoryWriteFrame s t #v[TwoOutputs.secondOutputRegion routine initial] := by
  obtain ⟨a, stateA, load, swapped⟩ := serialize_load_generic v routine frame offset capacity hashFits loadPC machine call state
    rsp rip words loadInside (loadCode state.loaded)
  have rspA : rspOf a = rspOf s := load.agrees.read (n := 64) (r := 4)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have memA (address : BitVec 64) : a.external[address]? = s.external[address]? := by
    apply load.agrees.byte
    cases v <;> simp [Serialize.effect, Effect.components, Component.Covers]
  have savedA : memLoad a.external (rspOf a + BitVec.ofNat 64 slot) 64 = initial.regValue .r8 := by
    rw [rspA]
    calc
      memLoad a.external (rspOf s + BitVec.ofNat 64 slot) 64 = memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 := by
        apply memLoad_congr
        intro i _
        change (a.external[_]?).getD 0 = (s.external[_]?).getD 0
        rw [memA]
      _ = _ := saved
  have ripA : a.RIP = storePC - 8#64 := load.rip.trans nextPC
  obtain ⟨b, stateB, ripB, outputB, wordsB, frameB⟩ :=
    serialize_second_pointer_generic v routine frame slot (storePC - 8#64)
      capacity slotFits slotLow machine call stateA (rspA.trans rsp) ripA savedA swapped
      (pointerCode stateA.loaded) (by simpa only [BitVec.sub_add_cancel] using target)
  have ripB' : b.RIP = storePC := by simpa only [BitVec.sub_add_cancel] using ripB
  have firstB : (TwoOutputs.outputRegion routine initial).HasBytes b.external first := by
    refine ⟨firstBytes.1, fun i => ?_⟩
    rw [frameB.byte (by simp [Component.Covers]), memA]
    exact firstBytes.2 i
  have secondRegion : (⟨(initial.regValue .r8).toNat, v.outputBytes⟩ : MemoryRegion) =
      TwoOutputs.secondOutputRegion routine initial := by
    simp only [TwoOutputs.secondOutputRegion, registerRegion, outputSize]
  have member : (⟨(initial.regValue .r8).toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion routine initial, TwoOutputs.secondOutputRegion routine initial] := by
    rw [secondRegion]
    simp
  obtain ⟨t, stateT, store, frameT, second⟩ := serialize_store_generic v routine storePC
    (if v = .sha224 then .r10 else .r11) (initial.regValue .r8) machine call stateB member
    (by cases v <;> exact outputB) wordsB ripB'
    storeInside (storeCode stateB.loaded)
  refine ⟨t, stateT, store.rip, serialize_preserves_first call firstB ?_, ?_, ?_, ?_⟩
  · simpa only [secondRegion] using frameT
  · simpa only [secondRegion] using second
  · have rspT : rspOf t = rspOf b := store.agrees.read (n := 64) (r := 4)
      (by cases v <;> simp [Serialize.effect, Effect.components])
    exact rspT.trans ((frameB.read (n := 64) (r := 4) (by cases v <;> simp)).trans rspA)
  · have writes : MemoryWriteFrame b t #v[TwoOutputs.secondOutputRegion routine initial] := by
      simpa only [secondRegion] using frameT
    intro address outside
    rw [writes address outside, frameB.byte (by simp [Component.Covers]), memA]

theorem serialized_last [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32} {first : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = (Finalization.resetLast.layout v).exit)
    (words : HashStateAt s (rspOf s + 64#64) hash)
    (saved : memLoad s.external (rspOf s + 192#64) 64 = initial.regValue .r8)
    (firstBytes : (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes s.external first) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      t.RIP = resetStorePC v true + BitVec.ofNat 64
        (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224))).length ∧
      (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes t.external first ∧
      (TwoOutputs.secondOutputRegion (resetRoutine v) initial).HasBytes t.external
        (if v == .sha224 then (serializeHash hash).extract 0 28 else serializeHash hash) ∧
      rspOf t = rspOf s ∧
      MemoryWriteFrame s t #v[TwoOutputs.secondOutputRegion (resetRoutine v) initial] := by
  apply serialized_last_generic v (resetRoutine v) 248 .at64 192
    (resetLoadPC v true) (resetStorePC v true)
    (by rw [resetRoutine_stack]; decide) (by decide) (by decide) (by decide)
    (by cases v <;> rfl) (by cases v <;> decide +kernel)
    (reset_load_inside v true) (fun loaded => reset_load_code v true loaded)
    ?_ ?_ (reset_store_inside v true) (fun loaded => reset_store_code v true loaded)
    machine call state rsp rip words saved firstBytes
  · intro t loaded
    have pc : resetStorePC v true - 8#64 = Extracted.textAddress +
        BitVec.ofNat 64 ((resetStorePC v true - 8#64).toNat - 0x100000) := by
      cases v <;> decide +kernel
    rw [pc]
    apply programText_slice (programLoaded_codeIn loaded)
    · cases v <;> decide +kernel
    · cases v <;> decide +kernel
  · have pc : resetStorePC v true = Extracted.textAddress +
        BitVec.ofNat 64 ((resetStorePC v true).toNat - 0x100000) := by
      cases v <;> decide +kernel
    rw [pc]
    exact inProgram_of_textOffset _ (by cases v <;> decide +kernel)

theorem serialized_first [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = (Finalization.resetFirst.layout v).exit)
    (words : HashStateAt s (rspOf s + 64#64) hash)
    (base : s.regValue .rbx = rspOf s + 64#64)
    (output : s.regValue .r13 = initial.regValue .rcx) :
    ∃ a b t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      (Serialize.effect (resetLoadPC v false) (.loadSwap .at64 (v == .sha224)) s).Holds s a ∧
      Initialize.Post (Initialization.resetOutput.layout v) (rspOf a) a b ∧
      (Serialize.effect (resetStorePC v false) (.store .r13 (v == .sha224)) b).Holds b t ∧
      HasherAt t (stackPtr initial - 248#64) ByteArray.empty v.initialHash ∧
      (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes t.external
        (if v == .sha224 then (serializeHash hash).extract 0 28 else serializeHash hash) ∧
      MemoryWriteFrame b t #v[TwoOutputs.outputRegion (resetRoutine v) initial] := by
  obtain ⟨a, stateA, load, swapped⟩ := serialize_load v (resetLoadPC v false) machine call state
    rsp rip words (reset_load_inside v false) (reset_load_code v false state.loaded)
  have rspA : rspOf a = rspOf s := load.agrees.read (n := 64) (r := 4)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have baseA : a.regValue .rbx = rspOf a + 64#64 := by
    rw [rspA]
    exact (load.agrees.read (n := 64) (r := 3)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans base
  have outputA : a.regValue .r13 = initial.regValue .rcx :=
    (load.agrees.read (n := 64) (r := 13)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans output
  have ripA : a.RIP = (Initialization.resetOutput.layout v).start :=
    load.rip.trans (reset_load_first_next v)
  obtain ⟨b, stateB, init⟩ := initialize_state v (occ := .resetOutput) machine call stateA
    (rspA.trans rsp) ripA (by simp) (fun _ => baseA)
  have outputB : b.regValue .r13 = initial.regValue .rcx := by
    apply Eq.trans (init.frame.read (n := 64) (r := 13) ?_) outputA
    cases v <;> simp [Initialize.Layout.components, Initialization.layout,
      Initialization.word, Initialization.temporary]
  have member : (⟨(initial.regValue .rcx).toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion (resetRoutine v) initial,
        TwoOutputs.secondOutputRegion (resetRoutine v) initial] := by
    cases v <;> simp [TwoOutputs.outputRegion, resetRoutine, registerRegion,
      sha224Reset, sha256Reset, Wrapper.Variant.outputBytes]
  obtain ⟨t, stateT, store, frameT, first⟩ := serialize_store v (resetStorePC v false)
    .r13 (initial.regValue .rcx) machine call stateB member outputB
    (resetOutput_preserves_swapped swapped init) init.rip
    (reset_store_inside v false) (reset_store_code v false stateB.loaded)
  have hashB : HasherAt b (stackPtr initial - 248#64) ByteArray.empty v.initialHash := by
    have h := init.hasher
    rw [rspA, rsp] at h
    exact h
  have stack : Stack.Valid initial 720 := by simpa only [resetRoutine_stack] using call.stack
  have pairs := call.separation.1
  simp only [List.pairwise_cons] at pairs
  have hasher : HasherAt t (stackPtr initial - 248#64) ByteArray.empty v.initialHash := by
    apply hashB.of_bytes
    intro i hi
    apply frameT
    intro region hr covered
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at hr
    subst region
    have firstContains : (TwoOutputs.outputRegion (resetRoutine v) initial).Contains
        (stackPtr initial - 248#64 + BitVec.ofNat 64 i).toNat := by
      cases v <;> exact covered
    apply pairs.1 (Stack.region initial (resetRoutine v).minStackBytes) (by simp) _ firstContains
    rw [resetRoutine_stack]
    exact stack_frame_contains stack (frame := 248) (offset := 0) (len := 104)
      (by decide) (by decide) ⟨i, hi, by simp⟩
  refine ⟨a, b, t, stateT, load, init, store, hasher, ?_, ?_⟩
  · cases v <;> exact first
  · cases v <;> exact frameT

end Sha2.Proofs.Reset
