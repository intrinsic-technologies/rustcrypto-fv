import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Lower
import P256.Proofs.SHA256.LengthEncoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SHA256

theorem first_head_result [Bindings]
    {initial s : RamState} {message chunk : ByteArray} {boundary : ReturnBoundary} {hash : Array UInt32}
    (pre : Message.Pre initial boundary message)
    (input : HashAt initial s boundary hash) (rip : s.RIP = 0x10d77e)
    (bytes : (⟨(stackPtr initial - 1048).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, HashAt initial t boundary hash ∧ t.RIP = 0x10d78b ∧
      (⟨(stackPtr initial - 1048).toNat, 64⟩ : MemoryRegion).HasBytes t.external chunk ∧
      memLoad t.external (stackPtr initial - 1120) 64 =
        memLoad t.external (stackPtr initial - 992) 64 ∧
      AgreesExcept [.reg 0,.mem (stackPtr initial - 1120) 8,.rip] s t := by
  have hp : Machine.FirstPre s := by
    refine ⟨rip, ?_, ?_, ?_⟩
    · rw [stack_address input.rsp]
      exact stack_readable pre input.toFrameState (offset := 992) (by decide) (by decide)
    · rw [stack_address input.rsp]
      exact stack_writable8 pre input.toFrameState (offset := 1120) (by decide) (by decide)
    · rw [stack_address input.rsp]
      exact stack_codeApart pre (offset := 1120) (codeOffset := 0xd77e) (by decide) (by decide) (by decide)
  obtain ⟨_, t, run, ready, _, effect⟩ := Machine.first_head boundary
    pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0xd77e Machine.firstBytes
      (by decide) (by decide +kernel)) hp
  have rsp : rspOf s = stackPtr initial - 1176 := input.rsp
  have frame : AgreesExcept [.reg 0,.mem (stackPtr initial - 1120) 8,.rip] s t := by
    simpa only [Machine.firstEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Nat.reduceDiv,
      Write.component, Operand.component, rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using effect.agrees
  have writes : Writes initial [.reg 0,.mem (stackPtr initial - 1120) 8,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    have w := writes_mem input.rsp (offset := 56) (len := 8) (.inr (by decide)) a
    rw [stack_address input.rsp] at w
    exact w ha
  have state := preserve pre input run ready frame writes (by simp) (by simp)
  have kept : ∀ i < 64,
      t.external[stackPtr initial - 1048 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 1048 + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨j, hj, he⟩ := ha
    apply OffsetsApart.ne (c₁ := -1120) (len₁ := 8) (c₂ := -1048) (len₂ := 64)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg] using he.symm
  refine ⟨t, state, effect.rip, ⟨bytes.1, ?_⟩, ?_, frame⟩
  · intro i
    have h := kept i.val (by have size : chunk.size = 64 := bytes.1; omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
      using h.trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
          using bytes.2 i)
  · have word := effect.writes.2
    change memLoad t.external (rspOf s+56) 64 = memLoad s.external (rspOf s+184) 64 at word
    have normalized : memLoad t.external (stackPtr initial-1120) 64 =
        memLoad s.external (stackPtr initial-992) 64 := by
      simpa only [rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word
    apply normalized.trans
    symm
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    have address : stackPtr initial - 1048 + BitVec.ofNat 64 (56+i) =
        stackPtr initial - 992 + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      rw [← BitVec.add_assoc (-1048#64) (56#64)]
      rfl
    have h := kept (56+i) (by omega)
    rw [address] at h
    simpa only [PhysicalMemory.read, BitVec.ofNat_eq_ofNat] using h

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
