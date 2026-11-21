import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Key.Short.Block
import Hkdf.Proofs.Common.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Short

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine (boundary_ne_program inProgram_of_textOffset
  programLoaded_codeIn programText_slice)
open Hkdf.Proofs.Common.Machine (supportedMachine_readyToStep memoryRegion_contains_add stack_region_end)

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (prepared : Prepared initial boundary s)
    (rip : s.RIP = 0x116380) (fits : key.size ≤ 64) :
    ∃ t, Ready initial boundary key t := by
  have avoids : ∀ region ∈ writeRegions initial, region.Avoids InProgram := by
    intro region member address contains inside
    exact ctx.avoids region (by simpa [writeRegions] using member)
      address contains (.inl inside)
  have stackBounds := stack_bounds ctx.toCalleePre
  change 720 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at stackBounds
  have savedBound : (stackPtr initial - 40).toNat + 48 ≤ 2^64 := by
    have base : (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 := by
      simpa only [BitVec.ofNat_eq_ofNat] using
        Hkdf.Proofs.Key.stack_sub_toNat ctx.toCalleePre (offset := 40) (by decide)
    rw [base]
    omega
  have blockBound : (blockAddress initial).toNat + 64 ≤ 2^64 := by
    change (stackPtr initial - 376).toNat + 64 ≤ 2^64
    have base : (stackPtr initial - 376).toNat = (stackPtr initial).toNat - 376 := by
      simpa only [BitVec.ofNat_eq_ofNat] using
        Hkdf.Proofs.Key.stack_sub_toNat ctx.toCalleePre (offset := 376) (by decide)
    rw [base]
    omega
  let layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 720 0 key.size 0 :=
    ⟨384, 0, 376, by decide, by decide, by decide, by decide, by decide,
      by omega, .inr (by omega)⟩
  let callLayout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 720 0 0 0 :=
    ⟨384, 0, 376, by decide, by decide, by decide, by decide, by decide,
      by decide, .inr (by decide)⟩
  have code := programText_slice (programLoaded_codeIn prepared.loaded) 0x16380
    [0x48,0x89,0xe7] (by decide) (by decide +kernel)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (mov_r64_r64_effect_step 0x116380 0x48 0xe7
      (by simp [RexWPrefix]) rfl).advances
      (supportedMachine_readyToStep prepared.machine) code rip
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x16383 (by decide)))
  have frameU : AgreesExcept [.reg 7,.rip] s u := effectU.agrees
  have memoryU : u.external = s.external := frameU.external (by simp [Component.Covers])
  have runningU := prepared.toRunning.of_agrees runU readyU frameU
    (by intro c hc a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl | rfl <;> exact ha.elim) avoids (by simp)
  have stateU := prepared.toState.of_observations runningU
    (by intro i hi; change u.external[_]? = s.external[_]?; rw [memoryU])
    (frameU.read (n := 64) (r := 5) (by simp))
    (frameU.mxcsr (by simp)) (frameU.fcw (by simp))
  have rspU : stackPtr u = blockAddress initial :=
    (frameU.read (n := 64) (r := 4) (by simp)).trans prepared.rsp
  have outputU : u.regValue .rdi = blockAddress initial := effectU.writes.trans prepared.rsp
  have inputU : u.regValue .rsi = initial.regValue .rsi :=
    (frameU.read (n := 64) (r := 6) (by simp)).trans prepared.inputPointer
  have lengthU : u.regValue .rdx = BitVec.ofNat 64 key.size := by
    rw [← ctx.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (frameU.read (n := 64) (r := 2) (by simp)).trans prepared.inputLength
  have zerosU : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes
      u.external ⟨Array.replicate 64 0⟩ := by
    rw [memoryU]
    exact prepared.zeroBlock
  have pointer := Hkdf.Proofs.Common.Memory.memcpy_pointer stateU.loaded
  have target : callMemPtr 0x116383 (.rip 0xeaf8f) u = 0x10dd60 := pointer.2
  have pushed : pushAddr u = stackPtr initial - 384 := by
    rw [pushAddr,rspU,blockAddress,BitVec.sub_sub]
    rfl
  have callWrites : WritesWithin
      (callEffect (callMemPtr 0x116383 (.rip 0xeaf8f)) 0x116389 u).components
      (writeRegions initial) := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, pushed,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨Stack.region initial stackBytes, by simp [writeRegions], ?_⟩
      exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub
        ctx.stack.2.2.1 (by decide) (by decide) ha
    · exact ha.elim
  have writable : MemWritable u (pushAddr u) 8 := by
    rw [pushed]
    exact stack_writable8 ctx stateU (by decide) (by decide)
  have callCode := programText_slice (programLoaded_codeIn stateU.loaded) 0x16383
    (encodeCallM64 (.rip 0xeaf8f)) (by decide) (by decide +kernel)
  have codeApart : RangeApart (pushAddr u) 8 0x116383 6 := by
    rw [pushed]
    exact stack_codeApart ctx (offset := 384) (len := 8)
      (codeOffset := 0x16383) (codeLen := 6) (by decide) (by decide) (by decide)
  obtain ⟨v, runningV, effectV, boundaryV⟩ := stateU.toRunning.call
    (call_m64_effect_step 0x116383 (.rip 0xeaf8f) trivial rfl rfl)
    callCode ⟨⟨⟨effectU.rip, writable, codeApart⟩, by rw [target]; decide⟩, pointer.1⟩
    (by
      rw [target]
      exact boundary_ne_program ctx.outerBoundary
        (inProgram_of_textOffset 0xdd60 (by decide))) callWrites avoids
  have frameV : AgreesExcept [.reg 4,.mem (stackPtr initial - 384) 8,.rip] u v := by
    simpa only [callEffect,pushEffect_components,pushed] using effectV.agrees
  have rspV : stackPtr v = stackPtr initial - 384 := effectV.writes.1.trans pushed
  have returnV : (returnBoundary v).rip = 0x116389 := congrArg ReturnBoundary.rip boundaryV
  have outputV : v.regValue .rdi = blockAddress initial :=
    (frameV.read (n := 64) (r := 7) (by simp)).trans outputU
  have inputV : v.regValue .rsi = initial.regValue .rsi :=
    (frameV.read (n := 64) (r := 6) (by simp)).trans inputU
  have lengthV : v.regValue .rdx = BitVec.ofNat 64 key.size :=
    (frameV.read (n := 64) (r := 2) (by simp)).trans lengthU
  have inputRegion : registerRegion v .rsi key.size = registerRegion initial .rsi key.size := by
    simp only [registerRegion,inputV]
  have inputAllocated : (registerRegion v .rsi key.size).Allocated v.external := by
    rw [inputRegion]
    intro a ha
    obtain ⟨byte,byteAt⟩ := ctx.inputAllocated a ha
    exact Option.isSome_iff_exists.mp (runningV.allocated a
      (by simp only [byteAt,Option.isSome_some]))
  have pre : CalleePre v boundary 0x10dd60 key.size key.size 0 :=
    callee_pre_of_stack_output ctx.stride ctx.stack (ctx.avoids _ (by simp)) ctx.outerBoundary
      runningV.machine runningV.directionFlag runningV.loaded runningV.allocated
      layout (effectV.rip.trans target) rspV outputV
      (by rw [returnV]; exact inProgram_of_textOffset 0x16389 (by decide))
      (by rw [inputRegion]; exact ctx.inputBounded) inputAllocated
      (by rw [inputRegion]; exact ctx.separation ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide))
  have callMemory : MemoryWriteFrame u v
      #v[registerRegion v .rdi 0, Stack.region v 0] := by
    apply frameV.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨Stack.region v 0, by simp, ?_⟩
      obtain ⟨i,hi,rfl⟩ := ha
      rw [← rspV]
      exact memoryRegion_contains_add pre.stack.1
        (by change (stackPtr v).toNat - 0 ≤ (stackPtr v).toNat; omega)
        (by rw [stack_region_end]; exact Nat.le_refl _) hi
    · exact ha.elim
  have savedApart := stack_layout_disjoint (savedOffset := 40) (savedBytes := 48)
    ctx.stack callLayout rspV outputV (.inl (by decide)) (by decide)
  have stateV := stateU.of_observations runningV
    (frame_agrees_of_disjoint callMemory savedBound savedApart)
    (frameV.read (n := 64) (r := 5) (by simp))
    (frameV.mxcsr (by simp)) (frameV.fcw (by simp))
  have zerosV : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes
      v.external ⟨Array.replicate 64 0⟩ :=
    frame_hasBytes callMemory
      (stack_layout_disjoint (savedOffset := 376) (savedBytes := 64)
        ctx.stack callLayout rspV outputV (.inl (by decide)) (by decide)) blockBound zerosU
  obtain ⟨w,result,copied,_⟩ := Hkdf.Proofs.Common.Memory.memcpy_correct pre lengthV (by omega)
  have writableWithin := stack_layout_within ctx.stack layout rspV outputV
  have runningW := runningV.of_callee result (by
    intro region member a ha
    exact ⟨Stack.region initial stackBytes, by simp [writeRegions],
      writableWithin region member a ha⟩)
  have savedApartW := stack_layout_disjoint (savedOffset := 40) (savedBytes := 48)
    ctx.stack layout rspV outputV (.inl (by dsimp only [layout]; omega))
      (by change 40 + 8 ≤ 384; decide)
  have stateW := stateV.of_observations runningW
    (frame_agrees_of_disjoint result.frame savedBound savedApartW)
    (result.abi.1 .rbp (by simp)) result.abi.2.2.1 result.abi.2.2.2
  have blockW := copied_block ctx stateV fits outputV inputV rspV zerosV result copied
  have codeW := programText_slice (programLoaded_codeIn stateW.loaded) 0x16389
    [0xe9,0xab,0x02,0x00,0x00] (by decide) (by decide +kernel)
  obtain ⟨t,runT,readyT,effectT⟩ := (jmp_rel32_effect_step 0x116389 0x2ab (by decide)).advances
    (supportedMachine_readyToStep stateW.machine) codeW
    (result.rip.trans returnV)
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x16639 (by decide)))
  have frameT : AgreesExcept [.rip] w t := effectT.agrees
  have memoryT : t.external = w.external := frameT.external (by simp [Component.Covers])
  have runningT := stateW.toRunning.of_agrees runT readyT frameT
    (by intro c hc a ha; have eq : c = .rip := by simpa using hc
        subst c; exact ha.elim) avoids (by simp)
  have stateT := stateW.of_observations runningT
    (by intro i hi; change t.external[_]? = w.external[_]?; rw [memoryT])
    (frameT.read (n := 64) (r := 5) (by simp))
    (frameT.mxcsr (by simp)) (frameT.fcw (by simp))
  refine ⟨t,⟨stateT,effectT.rip,?_,?_,?_⟩⟩
  · have kept : stackPtr t = stackPtr w := frameT.read (n := 64) (r := 4) (by simp)
    have returned : stackPtr w = stackPtr v + 8 := result.rsp
    change stackPtr t = blockAddress initial
    rw [kept,returned,rspV,blockAddress]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  · exact (frameT.read (n := 64) (r := 3) (by simp)).trans
      ((result.abi.1 .rbx (by simp)).trans
        ((frameV.read (n := 64) (r := 3) (by simp)).trans
          ((frameU.read (n := 64) (r := 3) (by simp)).trans prepared.outputPointer)))
  · rw [memoryT]
    exact blockW

end Hkdf.Proofs.Key.Short
