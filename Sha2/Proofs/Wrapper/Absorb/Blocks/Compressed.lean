import Sha2.Proofs.Wrapper.Absorb.Blocks.State
import Sha2.Proofs.Wrapper.Absorb.Blocks.Mathematics
import Sha2.Proofs.Wrapper.Absorb.Blocks.Compression
import Sha2.Proofs.Wrapper.Absorb.Blocks.Counter
import Sha2.Proofs.Wrapper.Absorb.LargeSetup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

structure CompressedSlice [Bindings] (initial s : RamState) (inputs : Array Program.Input)
    (index consumed : Nat) (v : Variant := .sha256) : Prop extends Preserved (v := v) initial s where
  remaining : index < inputs.size
  consumedBound : consumed ≤ inputs[index].bytes.size
  aligned : (prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size % 64 = 0
  hashWords : HashStateAt s (stackPtr initial - 88)
    (compressBlocks v.initialHash (prefixMessage inputs (index+1)))
  blocks : memLoad s.external (stackPtr initial - 56) 64 =
    BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size / 64)
  source : s.regValue .r13 = inputs[index].address + BitVec.ofNat 64 consumed
  length : s.regValue .rbp = BitVec.ofNat 64 (inputs[index].bytes.size - consumed)
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  countRegister : s.regValue .r15 = BitVec.ofNat 64 inputs.size

theorem compress [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context (v := v) initial inputs)
    (input : Input (v := v) initial s inputs index consumed)
    (rip : s.RIP = (v.pc 0x155))
    (count : s.regValue .rdx = BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/64)) :
    ∃ t, CompressedSlice (v := v) initial t inputs index consumed ∧ t.RIP = (v.pc 0x16d) := by
  obtain ⟨u, preservedU, ripU, blocksU, frameU⟩ := add_count ctx input.toPreserved rip
  have wordsU := hashState_of_bytes input.hashWords (by
    intro i hi
    apply frameU.byte
    intro c hc covers
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j,hj,eq⟩ := covers
      exact OffsetsApart.ne (c₁ := -56) (len₁ := 8) (c₂ := -88) (len₂ := 32)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by cases v <;> decide)
        (by simpa only [BitVec.sub_eq_add_neg] using eq.symm)
    · exact covers
    · exact covers)
  obtain ⟨mid, preservedV, setup⟩ := register_block (pc := (v.textOffset + 0x15d)) (bytes := LargeSetup.bytes)
    (effect := (fun s => LargeSetup.effect s v)) ctx preservedU
    (LargeSetup.run (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2)
    (by cases v <;> decide) (by cases v <;> decide +kernel) ripU
    (by simp [LargeSetup.effect,Effect.components,Component.Covers])
    (by simp [LargeSetup.effect,Effect.components])
    (by simp [LargeSetup.effect,Effect.components])
  have rdiV : mid.regValue .rdi = stackPtr initial-88 :=
    setup.writes.1.trans (stack_add preservedU.rsp (by cases v <;> decide))
  have sourceU : u.regValue .r13 = (inputs[index]'input.remaining).address + BitVec.ofNat 64 consumed :=
    (frameU.read (n := 64) (r := 13) (by simp)).trans input.source
  have rsiV : mid.regValue .rsi = (inputs[index]'input.remaining).address + BitVec.ofNat 64 consumed :=
    setup.writes.2.trans sourceU
  have rdxV : mid.regValue .rdx = BitVec.ofNat 64 (((inputs[index]'input.remaining).bytes.size-consumed)/64) :=
    (setup.agrees.read (n := 64) (r := 2) (by simp [LargeSetup.effect,Effect.components])).trans
      ((frameU.read (n := 64) (r := 2) (by simp)).trans count)
  have memoryV := setup.agrees.external (by simp [LargeSetup.effect,Effect.components,Component.Covers])
  have wordsV := hashState_of_bytes wordsU (fun i _ => by rw [memoryV])
  obtain ⟨t,preservedT,ripT,wordsT,abiT,frameT⟩ := compress_slice ctx preservedV
    ⟨index,input.remaining⟩ (by
      change consumed+64*(((inputs[index]'input.remaining).bytes.size-consumed)/64) ≤
        (inputs[index]'input.remaining).bytes.size
      have := input.consumedBound
      omega) setup.rip rdiV rsiV rdxV wordsV
  have hashEq := finish_hash v.initialHash (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  have counts := finish_counts (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  have blocksV : memLoad mid.external (stackPtr initial-56) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size/64) := by
    rw [memoryV,blocksU,input.blocks,count,← BitVec.ofNat_add,
      prefixMessage_succ inputs index input.remaining,counts.1]
  have blocksT : memLoad t.external (stackPtr initial-56) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size/64) := by
    rw [← blocksV]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (frame_bytes ctx frameT (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
        (by cases v <;> decide : 56 ≤ 344) (by cases v <;> decide : 8 ≤ 56) (.inr (by cases v <;> decide)) i hi)
  have kept (r : BitVec 5) (hr : r ∈ ([5,13,14,15] : List (BitVec 5))) :
      (Operand.reg r : Operand 64).read mid = (Operand.reg r : Operand 64).read s := by
    have hu : Component.reg r ∉ [.mem (stackPtr initial-56) 8,.flags,.rip] := by simp
    apply (setup.agrees.read (n := 64) (r := r) ?_).trans (frameU.read hu)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [LargeSetup.effect,Effect.components]
  refine ⟨t,⟨preservedT,input.remaining,input.consumedBound,input.aligned,?_,blocksT,
    (abiT.1 .r13 (by simp)).trans ((kept 13 (by simp)).trans input.source),
    (abiT.1 .rbp (by simp)).trans ((kept 5 (by simp)).trans input.length),
    (abiT.1 .r14 (by simp)).trans ((kept 14 (by simp)).trans input.indexRegister),
    (abiT.1 .r15 (by simp)).trans ((kept 15 (by simp)).trans input.countRegister)⟩,ripT⟩
  rw [prefixMessage_succ inputs index input.remaining,← hashEq]
  exact wordsT

theorem skip [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (input : Input (v := v) initial s inputs index consumed)
    (zero : ((inputs[index]'input.remaining).bytes.size-consumed)/64 = 0) :
    CompressedSlice (v := v) initial s inputs index consumed := by
  have hashEq := finish_hash v.initialHash (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  have counts := finish_counts (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes input.consumedBound input.aligned
  rw [zero,Nat.mul_zero,Nat.add_zero] at hashEq
  have empty : (inputs[index]'input.remaining).bytes.extract consumed consumed = ByteArray.empty := by simp
  rw [empty,compressBlocks_short _ _ (by cases v <;> decide)] at hashEq
  refine ⟨input.toPreserved,input.remaining,input.consumedBound,input.aligned,?_,?_,
    input.source,input.length,input.indexRegister,input.countRegister⟩
  · rw [prefixMessage_succ inputs index input.remaining,← hashEq]
    exact input.hashWords
  · rw [prefixMessage_succ inputs index input.remaining,counts.1,zero,Nat.add_zero]
    exact input.blocks

end Sha2.Proofs.Wrapper.Absorb.Blocks
