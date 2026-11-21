import Sha2.Proofs.Common.SHA256.Finalize.Proof.CallGeometry
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Bytes
import Sha2.Proofs.Wrapper.Hash.LengthEncoding
import Sha2.Proofs.Wrapper.Call

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem pad [Bindings] {L : Layout} {initial s : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n} {message : ByteArray}
    (ctx : Context L initial regions reserve) (state : ExecutionState initial s regions)
    (prepared : Prepared L (L.sp initial) message s) :
    ∃ t, Padded L initial s t regions message := by
  have tailBound : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have address : Mark.address L.variant s =
      L.buffer (L.sp initial) + BitVec.ofNat 64 (message.size % 64) := by
    simp only [Mark.address, show rspOf s = L.sp initial from prepared.rsp,
      prepared.tailLength, Layout.buffer]
  have pre : Mark.Pre L.entry L.variant s := by
    refine ⟨prepared.rip, ?_, ?_⟩
    · rw [address, Layout.buffer, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ctx.writable state (by have := ctx.wf.bufferFits; omega) (by decide)
    · rw [address, Layout.buffer, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ctx.codeApart (by have := ctx.wf.bufferFits; omega) (ctx.code.inside .mark)
  obtain ⟨_, marked, markRun, markReady, _, markEffect⟩ := ctx.blocks.mark s
    (supportedMachine_readyToStep state.machine) (ctx.code.loaded .mark s state.loaded) pre
  have markWrites : WritesWithin (Mark.effect L.entry L.variant s).components
      (footprint L (L.sp initial)) := by
    intro c hc a ha
    simp only [Mark.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
    refine ⟨⟨(L.buffer (L.sp initial)).toNat, 64⟩, by simp [footprint], ?_⟩
    rw [address, Layout.buffer, BitVec.add_assoc, ← BitVec.ofNat_add] at ha
    exact ctx.local_cover (base := L.variant.buffer.value) (offset := message.size % 64)
      (by have := ctx.wf.bufferFits; omega) (by omega) ha
  have preservedM := (Preserved.initial state prepared.rsp).of_agrees ctx markRun markReady
    markEffect.agrees markWrites
    (by
      intro r _ kept
      cases h : L.variant <;>
        simp_all [Mark.effect, Effect.components, Write.component, Operand.component,
          Variant.clobbered, Variant.padReg, Variant.hashReg, Variant.registers,
          Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks,
          Blocks.Length.Registers.preShifted])
    (by simp [Mark.effect, Effect.components])
  have markedBytes (i : Nat) (hi : i < 104) (ne : i ≠ message.size % 64) :
      marked.external[L.buffer (L.sp initial) + BitVec.ofNat 64 i]? =
        s.external[L.buffer (L.sp initial) + BitVec.ofNat 64 i]? := by
    apply markEffect.agrees.byte
    intro c hc ha
    simp only [Mark.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
    obtain ⟨j, hj, eq⟩ := ha
    have hj0 : j = 0 := by omega
    subst j
    rw [address, BitVec.add_zero] at eq
    have same := (BitVec.add_right_inj _).mp eq
    have natSame := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at natSame
    apply ne
    omega
  have writes := markEffect.writes
  change (.reg L.variant.padReg : Operand 64).read marked =
      (.reg L.variant.registers.tail : Operand 64).read s ^^^ 63 ∧
    memLoad marked.external (Mark.address L.variant s) 8 = 128 ∧
    marked.regValue .rdi = Mark.address L.variant s + 1 ∧
    marked.regValue .rsi = 0 ∧
    marked.regValue .rdx = (.reg L.variant.registers.tail : Operand 64).read s ^^^ 63 at writes
  have paddingLength : (.reg L.variant.padReg : Operand 64).read marked =
      BitVec.ofNat 64 (63 - message.size % 64) := by
    rw [writes.1, prepared.tailLength]
    exact Sha2.Proofs.Wrapper.Hash.tail_zero_count _ tailBound
  have destination : marked.regValue .rdi = L.buffer (L.sp initial) +
      BitVec.ofNat 64 (message.size % 64 + 1) := by
    rw [writes.2.2.1, address, BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  have count : marked.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64) := by
    rw [writes.2.2.2.2, prepared.tailLength]
    exact Sha2.Proofs.Wrapper.Hash.tail_zero_count _ tailBound
  have hashM : HashStateAt marked (L.hash (L.sp initial))
      (compressBlocks L.hashVariant.initialHash message) := by
    apply Sha2.Proofs.Wrapper.hashState_of_bytes prepared.hasher.hashWords
    intro i hi
    simpa only [Layout.hash, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat] using markedBytes (64 + i) (by omega) (by omega)
  have tailM : (.reg L.variant.registers.tail : Operand 64).read marked =
      BitVec.ofNat 64 (message.size % 64) := by
    exact (markEffect.agrees.read (n := 64) (r := L.variant.registers.tail) (by
      cases h : L.variant <;>
        simp [Mark.effect, Effect.components, Variant.registers, Variant.padReg,
          Blocks.Length.Registers.tail])).trans prepared.tailLength
  have blocksM : (.reg L.variant.registers.blocks : Operand 64).read marked = countValue L message := by
    exact (markEffect.agrees.read (n := 64) (r := L.variant.registers.blocks) (by
      cases h : L.variant <;>
        simp [Mark.effect, Effect.components, Variant.registers, Variant.padReg,
          Blocks.Length.Registers.blocks])).trans prepared.blocks
  have hashPointerM : L.variant.needsHashPointer = true →
      (.reg L.variant.hashReg : Operand 64).read marked = L.hash (L.sp initial) := by
    intro needs
    exact (markEffect.agrees.read (n := 64) (r := L.variant.hashReg) (by
      cases h : L.variant <;> simp_all [Mark.effect, Effect.components,
        Variant.needsHashPointer, Variant.hashReg, Variant.padReg])).trans (prepared.hashPointer needs)
  have markerM : marked.external[L.buffer (L.sp initial) +
      BitVec.ofNat 64 (message.size % 64)]? = some 128 := by
    have value := writes.2.1
    rw [address, memLoad_8] at value
    change ((marked.external[L.buffer (L.sp initial) + BitVec.ofNat 64 (message.size % 64)]?).getD 0).toBitVec = 128 at value
    cases byte : marked.external[L.buffer (L.sp initial) + BitVec.ofNat 64 (message.size % 64)]? with
    | none =>
      rw [byte] at value
      contradiction
    | some v =>
      simp only [byte, Option.getD_some] at value
      exact congrArg some (UInt8.eq_of_toBitVec_eq value)
  have markedRip : marked.RIP = L.fillCall := markEffect.rip.trans ctx.flow.mark
  have pointer := Sha2.Proofs.Wrapper.memset_pointer preservedM.state.loaded
  have pointerRead : MemReadable marked
      ((AddrMode.rip L.fillDisp).addr marked (L.fillCall + 6)) 8 := by
    change MemReadable marked (L.fillCall + 6 + L.fillDisp.signExtend 64) 8
    rw [ctx.flow.fillPointer]
    exact pointer.1
  have pointerValue : callMemPtr L.fillCall (.rip L.fillDisp) marked = 0x10dd10 := by
    change memLoad marked.external (L.fillCall + 6 + L.fillDisp.signExtend 64) 64 = _
    rw [ctx.flow.fillPointer]
    exact pointer.2
  obtain ⟨u, callRun, callReady, indirect⟩ :=
    (call_m64_effect_step L.fillCall (.rip L.fillDisp) trivial rfl rfl).advances
      markReady (ctx.code.loaded .fill marked preservedM.state.loaded)
      ⟨⟨ctx.pushPre preservedM.state preservedM.rsp markedRip (ctx.code.inside .fill),
        by rw [pointerValue]; decide⟩, pointerRead⟩
      (by change callMemPtr _ _ marked ≠ (returnBoundary initial).rip
          rw [pointerValue]
          exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xdd10 (by decide)))
  change (X86Proofs.callEffect (callMemPtr L.fillCall (.rip L.fillDisp))
    (L.fillCall + 6) marked).Holds marked u at indirect
  have callEffect : (X86Proofs.callEffect (fun _ => 0x10dd10) (L.fillCall + 6) marked).Holds marked u := by
    simpa only [X86Proofs.callEffect, pushEffect, pointerValue] using indirect
  have slot : pushAddr marked = L.sp initial - 8 := by
    rw [pushAddr, preservedM.rsp]
  have callFrame : AgreesExcept [.reg 4, .mem (L.sp initial - 8) 8, .rip] marked u := by
    simpa only [X86Proofs.callEffect, pushEffect_components, slot] using callEffect.agrees
  have rspU : stackPtr u = L.sp initial - 8 := callEffect.writes.1.trans slot
  have destinationU : u.regValue .rdi = L.buffer (L.sp initial) +
      BitVec.ofNat 64 (message.size % 64 + 1) :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans destination
  have zeroU : u.regValue .rsi = 0 :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans writes.2.2.2.1
  have countU : u.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64) :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans count
  have callWrites := ctx.callWrites preservedM.rsp (fun _ => 0x10dd10) (L.fillCall + 6)
  have callMemory := callEffect.agrees.memoryWriteFrame callWrites
  have loadedU : ProgramLoaded u := by
    intro a byte fetch
    rw [callMemory a]
    · exact preservedM.state.loaded a byte fetch
    · intro region member contains
      exact ctx.footprint_avoids region member a contains ⟨byte, fetch⟩
  have returnInProgram : InProgram (returnBoundary u).rip := by
    change InProgram (stackTop u)
    rw [(callEffect_stack callEffect).1, ctx.flow.fill]
    simpa only [Stage.pc, BitVec.add_zero] using ctx.code.inside .branch 0 (Nat.zero_le _)
  have calleePre : CalleePre u (returnBoundary initial) 0x10dd10 0
      (63 - message.size % 64) 0 := by
    apply callee_pre_of_input ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress
      (supportedMachine_of_ready_agrees preservedM.state.machine callReady callFrame)
      (callFrame.directionFlagClear (by simp) preservedM.state.directionFlag) loadedU
      (fun a ha => callFrame.grow a (preservedM.state.allocated a ha))
      (L.frameBytes + 8) (L.frameBytes - (L.variant.buffer.value + (message.size % 64 + 1)))
      ctx.wf.aligned (by have := ctx.wf.capacity; omega) (by omega)
      (by have := ctx.wf.bufferFits; omega)
      (by simp [registerRegion, MemoryRegion.Bounded, zeroU, userAddressLimit])
      (by intro a ha; have := ha.1; have := ha.2; simp only [registerRegion, MemoryRegion.Contains] at *; omega)
      (by intro a ha; have := ha.1; have := ha.2; simp only [registerRegion, MemoryRegion.Contains] at *; omega)
      callEffect.rip
    · rw [rspU]
      change stackPtr initial - BitVec.ofNat 64 L.frameBytes - 8 = _
      rw [BitVec.sub_sub, BitVec.ofNat_add]
      rfl
    · rw [destinationU, Layout.buffer, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact L.address initial (by have := ctx.wf.bufferFits; omega)
    · exact returnInProgram
  obtain ⟨t, result, filled, fillFrame⟩ := Common.Memory.memset_zero_correct calleePre
    (by rw [zeroU]; rfl) countU (by omega) returnInProgram
  have calleeWithin : ∀ region ∈ #v[registerRegion u .rdi (63 - message.size % 64), Stack.region u 0],
      ∀ a, region.Contains a → ∃ outer ∈ footprint L (L.sp initial), outer.Contains a := by
    intro region member a contains
    have cases : region = registerRegion u .rdi (63 - message.size % 64) ∨ region = Stack.region u 0 := by
      simpa using member
    rcases cases with rfl | rfl
    · refine ⟨⟨(L.buffer (L.sp initial)).toNat, 64⟩, by simp [footprint], ?_⟩
      change (u.regValue .rdi).toNat ≤ a ∧ a < (u.regValue .rdi).toNat + (63 - message.size % 64) at contains
      rw [destinationU, Layout.buffer, BitVec.add_assoc, ← BitVec.ofNat_add,
        ctx.address_toNat (by have := ctx.wf.bufferFits; omega)] at contains
      change (L.sp initial + BitVec.ofNat 64 L.variant.buffer.value).toNat ≤ a ∧
        a < (L.sp initial + BitVec.ofNat 64 L.variant.buffer.value).toNat + 64
      rw [ctx.address_toNat (by have := ctx.wf.bufferFits; omega)]
      omega
    · exact ⟨⟨(L.sp initial - 344).toNat, 344⟩, by simp [footprint],
        ctx.calleeStack_contains rspU (by decide) contains⟩
  have preserved := preservedM.of_call_result ctx callRun callEffect callWrites result calleeWithin
  have callBytes (i : Nat) (hi : i < 104) :
      u.external[L.buffer (L.sp initial) + BitVec.ofNat 64 i]? =
        marked.external[L.buffer (L.sp initial) + BitVec.ofNat 64 i]? := by
    apply callFrame.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    have apart : OffsetsApart (-8) 8 (BitVec.ofNat 64 L.variant.buffer.value) 104 := by
      cases L.variant <;> unfold OffsetsApart <;> decide +kernel
    apply apart.ne (L.sp initial) hj hi (by decide)
    simpa only [Layout.buffer, BitVec.sub_eq_add_neg] using eq.symm
  have fillBytes (i : Nat) (hi : i < 104) (kept : i < message.size % 64 + 1 ∨ 64 ≤ i) :
      t.external[L.buffer (L.sp initial) + BitVec.ofNat 64 i]? =
        marked.external[L.buffer (L.sp initial) + BitVec.ofNat 64 i]? := by
    refine Eq.trans (fillFrame.byte ?_) (callBytes i hi)
    intro c hc covered
    have memCovered : (Component.mem (u.regValue .rdi) (63 - message.size % 64)).Covers
        (L.buffer (L.sp initial) + BitVec.ofNat 64 i) := by
      cases c <;> simp_all [Common.Memory.Fill.fillComponents,
        Common.Memory.Fill.registerComponents, Component.Covers]
    obtain ⟨j, hj, eq⟩ := memCovered
    rw [destinationU, BitVec.add_assoc, ← BitVec.ofNat_add] at eq
    have same := (BitVec.add_right_inj _).mp eq
    have natSame := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at natSame
    rcases kept with low | high <;> omega
  have frame := callFrame.trans fillFrame
  refine ⟨t, preserved, result.rip.trans ((callEffect_stack callEffect).1.trans ctx.flow.fill),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Sha2.Proofs.Wrapper.hashState_of_bytes hashM
    intro i hi
    simpa only [Layout.hash, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      using fillBytes (64 + i) (by omega) (.inr (by omega))
  · exact (frame.read (n := 64) (r := L.variant.registers.tail) (by
      cases h : L.variant <;> simp [Common.Memory.Fill.fillComponents,
        Common.Memory.Fill.registerComponents, Variant.registers, Blocks.Length.Registers.tail])).trans tailM
  · exact (frame.read (n := 64) (r := L.variant.registers.blocks) (by
      cases h : L.variant <;> simp [Common.Memory.Fill.fillComponents,
        Common.Memory.Fill.registerComponents, Variant.registers, Blocks.Length.Registers.blocks])).trans blocksM
  · exact (frame.read (n := 64) (r := L.variant.padReg) (by
      cases h : L.variant <;> simp [Common.Memory.Fill.fillComponents,
        Common.Memory.Fill.registerComponents, Variant.padReg])).trans paddingLength
  · intro needs
    exact (frame.read (n := 64) (r := L.variant.hashReg) (by
      cases h : L.variant <;> simp [Common.Memory.Fill.fillComponents,
        Common.Memory.Fill.registerComponents, Variant.hashReg])).trans (hashPointerM needs)
  · apply Sha2.Proofs.Wrapper.Hash.Finalize.Pad.padded_bytes
    · refine ⟨prepared.hasher.tailBytes.1, ?_⟩
      intro i
      have hi : i.val < message.size % 64 := by
        simpa only [remainderBytes_size] using i.isLt
      change t.external[BitVec.ofNat 64 ((L.buffer (L.sp initial)).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        fillBytes i.val (by omega) (.inl (by omega)), markedBytes i.val (by omega) (by omega)]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        using prepared.hasher.tailBytes.2 i
    · exact (fillBytes _ (by omega) (.inl (by omega))).trans markerM
    · intro i hi
      have byte := filled i hi
      rw [destinationU] at byte
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using byte

end Sha2.Proofs.Common.SHA256.Finalize
