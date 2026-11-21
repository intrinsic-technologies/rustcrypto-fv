import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Extract.Memory
import Hkdf.Proofs.Standard.Extract.Epilogue
import Hkdf.Proofs.Standard.Extract.Output

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Extract

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

theorem restored {initial s t : RamState} (saved : SavedStackAt initial s)
    (rsp : rspOf s = frameBase initial) (effect : (Epilogue.effect s).Holds s t) :
    CalleeSavedRegistersUnchanged initial t := by
  intro register member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · have value : t.regValue .rbx = memLoad s.external (rspOf s + 472) 64 :=
      effect.writes.2.1
    rw [rsp] at value
    have addr : frameBase initial + 472 = initial.regValue .rsp - 48 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at value
    exact value.trans (saved.words (.rbx, 48) (by simp))

  · have value : t.regValue .rbp = memLoad s.external (rspOf s + 512) 64 :=
      effect.writes.2.2.2.2.2.2
    rw [rsp] at value
    have addr : frameBase initial + 512 = initial.regValue .rsp - 8 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at value
    exact value.trans (saved.words (.rbp, 8) (by simp))

  · have value : t.regValue .r12 = memLoad s.external (rspOf s + 480) 64 :=
      effect.writes.2.2.1
    rw [rsp] at value
    have addr : frameBase initial + 480 = initial.regValue .rsp - 40 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at value
    exact value.trans (saved.words (.r12, 40) (by simp))

  · have value : t.regValue .r13 = memLoad s.external (rspOf s + 488) 64 :=
      effect.writes.2.2.2.1
    rw [rsp] at value
    have addr : frameBase initial + 488 = initial.regValue .rsp - 32 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at value
    exact value.trans (saved.words (.r13, 32) (by simp))

  · have value : t.regValue .r14 = memLoad s.external (rspOf s + 496) 64 :=
      effect.writes.2.2.2.2.1
    rw [rsp] at value
    have addr : frameBase initial + 496 = initial.regValue .rsp - 24 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at value
    exact value.trans (saved.words (.r14, 24) (by simp))

  · have value : t.regValue .r15 = memLoad s.external (rspOf s + 504) 64 :=
      effect.writes.2.2.2.2.2.1
    rw [rsp] at value
    have addr : frameBase initial + 504 = initial.regValue .rsp - 16 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at value
    exact value.trans (saved.words (.r15, 16) (by simp))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem finish [bindings : Bindings]
    {initial s : RamState} {salt : Option ByteArray} {inputs : Array Input}
    {digest : ByteArray} (ctx : Standard.Context initial salt inputs)
    (state : Standard.State initial s) (rip : s.RIP = 0x10174c)
    (rsp : stackPtr s = Standard.frameBase initial)
    (pointer : memLoad s.external (Standard.frameBase initial + 96) 64 = initial.regValue .r9)
    (bytes : (⟨(Standard.hmacBase initial).toNat,32⟩ : MemoryRegion).HasBytes s.external digest) :
    ∃ fuel t, Returns (returnBoundary initial) fuel s t ∧
      SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      t.RIP = (returnBoundary initial).rip ∧ stackPtr t = (returnBoundary initial).rsp ∧
      MemoryWriteFrame s t #v[outputRegion initial hkdfSha256Extract,
        Stack.region initial hkdfSha256Extract.minStackBytes] ∧
      readOutput (outputRegion initial hkdfSha256Extract) t.external = .ok digest := by
  have outside := (Standard.returnBoundary_valid ctx).2.2
  have ptr : Copy.outputPtr s = initial.regValue .r9 := by
    change memLoad s.external (stackPtr s + 96) 64 = _
    rw [rsp]
    exact pointer
  obtain ⟨copyFuel, copied, copyRun, copyReady, _, copyEffect⟩ :=
    Copy.run (returnBoundary initial) outside s
      (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.machine)
      (Copy.code state.loaded) (copy_pre ctx state rip rsp pointer)
  have copyFrame := copy_agrees rsp ptr copyEffect
  have copiedSaved := copy_saved ctx state copyFrame
  have copiedRsp : rspOf copied = frameBase initial :=
    (copyFrame.read (n := 64) (r := 4) (by simp [copyComponents])).trans rsp
  have copiedWriteFrame := copy_writeFrame ctx copyFrame
  have copiedLoaded := Common.Machine.programLoaded_of_separation copiedWriteFrame
    state.loaded ctx.call.outputSeparation
  have readable (offset : Nat) (bound : offset ≤ 1792) :
      MemReadable copied (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
    have original := Standard.stack_readable ctx state (len := 8) bound (by omega)
    exact ⟨original.low, fun i hi ↦ copyFrame.grow _ (original.mem i hi)⟩
  have pre : Epilogue.Pre copied := by
    refine ⟨copyEffect.rip, ?_⟩
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [copiedRsp, frameBase, Hkdf.Proofs.Common.Machine.stackPtr_eq_regValue_rsp,
        Nat.reduceMul, Nat.reduceAdd,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using readable 48 (by decide)
    · simpa only [copiedRsp, frameBase, Hkdf.Proofs.Common.Machine.stackPtr_eq_regValue_rsp,
        Nat.reduceMul, Nat.reduceAdd,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using readable 40 (by decide)
    · simpa only [copiedRsp, frameBase, Hkdf.Proofs.Common.Machine.stackPtr_eq_regValue_rsp,
        Nat.reduceMul, Nat.reduceAdd,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using readable 32 (by decide)
    · simpa only [copiedRsp, frameBase, Hkdf.Proofs.Common.Machine.stackPtr_eq_regValue_rsp,
        Nat.reduceMul, Nat.reduceAdd,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using readable 24 (by decide)
    · simpa only [copiedRsp, frameBase, Hkdf.Proofs.Common.Machine.stackPtr_eq_regValue_rsp,
        Nat.reduceMul, Nat.reduceAdd,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using readable 16 (by decide)
    · simpa only [copiedRsp, frameBase, Hkdf.Proofs.Common.Machine.stackPtr_eq_regValue_rsp,
        Nat.reduceMul, Nat.reduceAdd,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using readable 8 (by decide)
  obtain ⟨epilogueFuel, returned, epilogueRun, epilogueReady, _, epilogueEffect⟩ :=
    Epilogue.run (returnBoundary initial) outside copied copyReady
      (Epilogue.code copiedLoaded) pre
  have epilogueNoMem : ∀ c ∈ (Epilogue.effect copied).components, ∀ a, ¬ c.Covers a := by
    simp [Epilogue.effect, Effect.components, Component.Covers]
  have epilogueMemory : returned.external = copied.external :=
    epilogueEffect.agrees.external epilogueNoMem
  have returnedRsp : stackPtr returned = stackPtr initial := by
    have word : stackPtr returned = rspOf copied + 520 := epilogueEffect.writes.1
    rw [word, copiedRsp, frameBase]
    exact BitVec.sub_add_cancel _ _
  have top : stackTop returned = (returnBoundary initial).rip := by
    change memLoad returned.external (stackPtr returned) 64 = _
    rw [returnedRsp, epilogueMemory]
    exact copiedSaved.returnAddress
  have returnedRead : MemReadable returned (stackPtr returned) 8 := by
    rw [returnedRsp]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using
      (readable 0 (by decide)).of_external_eq epilogueMemory
  have returnedLoaded : ProgramLoaded returned := by
    intro a b hb
    rw [epilogueMemory]
    exact copiedLoaded a b hb
  obtain ⟨final, step, finalReady, ret⟩ := (ret_effect_step 0x1017a2) returned epilogueReady
    (programText_slice (programLoaded_codeIn returnedLoaded) 0x17a2 [0xc3]
      (by decide) (by decide +kernel))
    ⟨⟨epilogueEffect.rip, returnedRead⟩, top ▸ (Standard.returnBoundary_valid ctx).2.1⟩
  have finalRsp : stackPtr final = (returnBoundary initial).rsp := by
    have word : stackPtr final = stackPtr returned + 8 := ret.writes
    rw [word, returnedRsp]
    rfl
  have finalRip : final.RIP = (returnBoundary initial).rip := ret.rip.trans top
  have returnRun := Returns.of_step step finalRip finalRsp
  have finalMemory : final.external = copied.external :=
    (ret.agrees.external (by simp [Component.Covers])).trans epilogueMemory
  have agrees := (copyFrame.trans epilogueEffect.agrees).trans ret.agrees
  have restoredSaved := restored copiedSaved copiedRsp epilogueEffect
  have saved : CalleeSavedRegistersUnchanged initial final := by
    intro register member
    have previous := restoredSaved register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (ret.agrees.read (n := 64) (r := 3) (by simp)).trans previous
    · exact (ret.agrees.read (n := 64) (r := 5) (by simp)).trans previous
    · exact (ret.agrees.read (n := 64) (r := 12) (by simp)).trans previous
    · exact (ret.agrees.read (n := 64) (r := 13) (by simp)).trans previous
    · exact (ret.agrees.read (n := 64) (r := 14) (by simp)).trans previous
    · exact (ret.agrees.read (n := 64) (r := 15) (by simp)).trans previous
  have outputWords : ∀ j < 4,
      memLoad final.external (initial.regValue .r9 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (hmacBase initial + BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    rw [finalMemory]
    have stores := copyEffect.writes
    simp only [Copy.effect, Write.AllHold, ptr] at stores
    have source : rspOf s = frameBase initial := rsp
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read,
        source, hmacBase, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read,
        source, hmacBase, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read,
        source, hmacBase, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read,
        source, hmacBase, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
  have finalRead : MemReadable final (initial.regValue .r9) 32 := by
    have original := output_readable ctx state
    exact ⟨original.low, fun i hi ↦ agrees.grow _ (original.mem i hi)⟩
  have output : (outputRegion initial hkdfSha256Extract).HasBytes final.external digest := by
    have size : digest.size = 32 := bytes.1
    have source (i : Nat) (hi : i < 32) :
        s.external[hmacBase initial + BitVec.ofNat 64 i]? = some digest[i] := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        bytes.2 ⟨i, by omega⟩
    refine ⟨size, ?_⟩
    intro i
    have bound : i.val < 32 := by omega
    have out := Bytes.of_memLoad (n := 64)
      (a := initial.regValue .r9 + BitVec.ofNat 64 (8*(i.val/8))) (m := final.external)
      (by intro k hk; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact finalRead.mem _ (by omega))
    have inp := Bytes.of_memLoad (n := 64)
      (a := hmacBase initial + BitVec.ofNat 64 (8*(i.val/8))) (m := s.external)
      (by intro k hk; rw [BitVec.add_assoc, ← BitVec.ofNat_add, source _ (by omega)]; trivial)
    have outByte := out (i.val%8) (by omega)
    have inByte := inp (i.val%8) (by omega)
    rw [outputWords (i.val/8) (by omega)] at outByte
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 8*(i.val/8) + i.val%8 = i.val by omega] at outByte inByte
    rw [← inByte, source _ bound] at outByte
    simpa only [outputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using outByte
  refine ⟨copyFuel+epilogueFuel+1, final, (copyRun.trans epilogueRun).returns returnRun,
    (Hkdf.Proofs.Common.Machine.supportedMachine_of_ready_agrees state.machine finalReady agrees).supported,
    Common.Machine.machineRamUnitStrideDecodable_of_ready finalReady ctx.environment.stringStride,
    saved, ret.agrees.directionFlagClear (by simp)
      (epilogueEffect.agrees.directionFlagClear
        (by simp [Epilogue.effect, Effect.components])
        (copyFrame.directionFlagClear (by simp [copyComponents]) state.directionFlag)),
    finalRip, finalRsp, ?_,
    readOutput_of_hasBytes output⟩
  · intro a outsideRegions
    rw [finalMemory]
    exact copiedWriteFrame a outsideRegions

end Hkdf.Proofs.Standard.Extract
