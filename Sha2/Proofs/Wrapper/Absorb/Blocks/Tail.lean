import Sha2.Proofs.Wrapper.Absorb.Blocks.Compressed
import Sha2.Proofs.Wrapper.Absorb.Blocks.TailRegisters
import Sha2.Proofs.Wrapper.Absorb.Arithmetic
import Sha2.Proofs.Wrapper.Absorb.TailLength
import Sha2.Proofs.Wrapper.Absorb.TailSetup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

theorem tail [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context (v := v) initial inputs)
    (input : CompressedSlice (v := v) initial s inputs index consumed) (rip : s.RIP = (v.pc 0x16d)) :
    ∃ t, Result (v := v) initial t inputs index := by
  let bytes := (inputs[index]'input.remaining).bytes
  let count := bytes.size-consumed
  have countBound : count < 2^32 := by
    have h := validCall_input_bounded ctx.call (⟨index,input.remaining⟩ : Fin inputs.size)
    change (inputs[index]'input.remaining).address.toNat + bytes.size < 2^32 at h
    dsimp only [count]
    omega
  have lengthNat : (s.regValue .rbp).toNat = count := by
    rw [input.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by change count < 2^64; omega)]
  have countSmall : count%64 < 64 := Nat.mod_lt _ (by cases v <;> decide)
  obtain ⟨u,preservedU,registers⟩ := register_block (pc := (v.textOffset + 0x16d)) (bytes := TailRegisters.bytes)
    (effect := (fun s => TailRegisters.effect s v)) ctx input.toPreserved
    (TailRegisters.run (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2)
    (by cases v <;> decide) (by cases v <;> decide +kernel) rip
    (by simp [TailRegisters.effect,Effect.components,Component.Covers])
    (by simp [TailRegisters.effect,Effect.components])
    (by simp [TailRegisters.effect,Effect.components])
  have memoryU := registers.agrees.external
    (by simp [TailRegisters.effect,Effect.components,Component.Covers])
  have sourceU : u.regValue .r13 =
      (inputs[index]'input.remaining).address + BitVec.ofNat 64 (consumed+64*(count/64)) := by
    have value : u.regValue .r13 = s.regValue .r13 + (0x7fffffffffffffc0 &&& s.regValue .rbp) :=
      registers.writes.2.2.2
    rw [value,full_length _ (by rw [lengthNat]; omega),lengthNat,input.source,
      BitVec.ofNat_add,BitVec.add_assoc]
  have lengthU : u.regValue .rbp = BitVec.ofNat 64 (count%64) :=
    registers.writes.2.2.1.trans ((tail_length _).trans (by rw [lengthNat]))
  obtain ⟨mid,preservedV,ripV,byteV,frameV⟩ := store_length ctx preservedU true registers.rip
  have tailV : mid.external[stackPtr initial-89]? = some (UInt8.ofNat (count%64)) := by
    change mid.external[stackPtr initial-89]? = some (UInt8.ofNat ((u.regValue .rbp).setWidth 8).toNat) at byteV
    rw [lengthU] at byteV
    simpa only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : count%64 < 2^64),
      Nat.mod_eq_of_lt (by omega : count%64 < 2^8)] using byteV
  have sourceV := (frameV.read (n := 64) (r := 13) (by simp)).trans sourceU
  have lengthV := (frameV.read (n := 64) (r := 5) (by simp)).trans lengthU
  have wordsV : HashStateAt mid (stackPtr initial-88)
      (compressBlocks v.initialHash (prefixMessage inputs (index+1))) := by
    apply hashState_of_bytes input.hashWords
    intro i hi
    exact (store_bytes frameV (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide) i hi).trans
      (by rw [memoryU]; rfl)
  have blocksV : memLoad mid.external (stackPtr initial-56) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size/64) := by
    rw [← input.blocks]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      ((store_bytes frameV (offset := 56) (len := 8)
        (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide) i hi).trans (by rw [memoryU]; rfl))
  obtain ⟨w,preservedW,setup⟩ := register_block (pc := (v.textOffset + 0x18b)) (bytes := TailSetup.bytes)
    (effect := (fun s => TailSetup.effect s v)) ctx preservedV
    (TailSetup.run (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2)
    (by cases v <;> decide) (by cases v <;> decide +kernel)
    (ripV.trans (by cases v <;> rfl))
    (by simp [TailSetup.effect,Effect.components,Component.Covers])
    (by simp [TailSetup.effect,Effect.components])
    (by simp [TailSetup.effect,Effect.components])
  have destinationW : w.regValue .rdi = stackPtr initial-152+BitVec.ofNat 64 0 := by
    exact (setup.writes.1.trans (stack_add preservedV.rsp (by cases v <;> decide))).trans (BitVec.add_zero _).symm
  have sourceW := setup.writes.2.1.trans sourceV
  have lengthW := setup.writes.2.2.trans lengthV
  have memoryW := setup.agrees.external (by simp [TailSetup.effect,Effect.components,Component.Covers])
  have endEq : consumed+64*(count/64)+count%64 = bytes.size := by
    have := input.consumedBound
    change consumed ≤ bytes.size at this
    dsimp only [count]
    omega
  obtain ⟨t,copied⟩ := Copy.copy ctx preservedW .tail ⟨index,input.remaining⟩
    (offset := consumed+64*(count/64)) (position := 0) (count := count%64)
    (by change consumed+64*(count/64)+count%64 ≤ bytes.size; omega)
    (by omega) setup.rip destinationW sourceW lengthW
  have wordsT : HashStateAt t (stackPtr initial-88)
      (compressBlocks v.initialHash (prefixMessage inputs (index+1))) := by
    apply hashState_of_bytes wordsV
    intro i hi
    exact (frame_bytes ctx copied.frame (by cases v <;> decide) (by omega) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide : 88 ≤ 344) (by cases v <;> decide : 32 ≤ 88) (.inr (by omega)) i hi).trans (by rw [memoryW]; rfl)
  have blocksT : memLoad t.external (stackPtr initial-56) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size/64) := by
    rw [← blocksV]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      ((frame_bytes ctx copied.frame (by cases v <;> decide) (by omega) (by cases v <;> decide) (by cases v <;> decide)
        (by cases v <;> decide : 56 ≤ 344) (by cases v <;> decide : 8 ≤ 56) (.inr (by omega)) i hi).trans (by rw [memoryW]; rfl))
  have tailT : t.external[stackPtr initial-89]? = some (UInt8.ofNat (count%64)) := by
    have kept := frame_bytes ctx copied.frame (by cases v <;> decide) (by omega) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide : 89 ≤ 344) (by cases v <;> decide : 1 ≤ 89) (.inr (by omega)) 0 (by cases v <;> decide)
    simp only [BitVec.add_zero,memoryW] at kept
    exact kept.trans tailV
  have counts := finish_counts (prefixMessage inputs index) bytes input.consumedBound input.aligned
  have sizeEq : (prefixMessage inputs (index+1)).size%64 = count%64 := by
    rw [prefixMessage_succ inputs index input.remaining]
    exact counts.2
  have tailEq : (prefixMessage inputs (index+1)).extract
      (64*((prefixMessage inputs (index+1)).size/64)) (prefixMessage inputs (index+1)).size =
      bytes.extract (consumed+64*(count/64)) bytes.size := by
    change remainderBytes (prefixMessage inputs (index+1)) = _
    rw [prefixMessage_succ inputs index input.remaining]
    exact finish_tail (prefixMessage inputs index) bytes input.consumedBound input.aligned
  have kept (r : BitVec 5) (hr : r ∈ ([14,15] : List (BitVec 5))) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read s := by
    apply (setup.agrees.read (n := 64) (r := r) ?_).trans
      ((frameV.read (n := 64) (r := r) (by simp)).trans (registers.agrees.read (n := 64) (r := r) ?_))
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    all_goals rcases hr with rfl | rfl
    all_goals simp [TailSetup.effect,TailRegisters.effect,Effect.components]
  refine ⟨t,⟨⟨copied.preserved,wordsT,?_,?_,blocksT⟩,copied.rip.trans (Variant.pc_add v 0x199 6),
    (copied.abi.1 .r14 (by simp)).trans ((kept 14 (by simp)).trans input.indexRegister),
    (copied.abi.1 .r15 (by simp)).trans ((kept 15 (by simp)).trans input.countRegister)⟩⟩
  · rw [sizeEq,tailEq]
    have result := copied.bytes
    change (⟨(stackPtr initial-152+0#64).toNat,count%64⟩ : MemoryRegion).HasBytes t.external
      (bytes.extract (consumed+64*(count/64)) (consumed+64*(count/64)+count%64)) at result
    rw [BitVec.add_zero,endEq] at result
    exact result
  · rw [sizeEq]
    exact tailT

end Sha2.Proofs.Wrapper.Absorb.Blocks
