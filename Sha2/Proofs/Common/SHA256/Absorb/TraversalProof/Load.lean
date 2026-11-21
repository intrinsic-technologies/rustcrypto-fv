import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Context

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve index : Nat}
    {regions : Vector MemoryRegion n} {inputs : Array Input}

theorem load_iteration (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions)
    (loop : LoopState l (l.chunk.sp initial) inputs index s)
    (data : InputData l (l.chunk.sp initial) inputs s)
    (separation : Separation l initial s reserve inputs) :
    ∃ t, ExecutionState initial t regions ∧ LoadPost l (l.chunk.sp initial) s t ∧
      Absorb.Prepared l.chunk (l.chunk.sp initial) (Wrapper.prefixMessage inputs index)
        (inputs[index]'loop.remaining) t := by
  have shifted : Blocks.readReg s l.index <<< 3 = BitVec.ofNat 64 (8 * index) := by
    rw [loop.indexRegister, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 index * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have pre : LoadPre l (l.chunk.sp initial) s := {
    rip := loop.rip
    rsp := loop.rsp
    pointerSlot := ctx.readable state ctx.wf.pointerFits
    lengthSlot := ctx.readable state ctx.wf.lengthFits
    pointer := by
      rw [shifted]
      exact Common.Memory.memReadable_sub data.pointersReadable (8 * index) 8 (by
        have remaining := loop.remaining
        omega)
    length := by
      rw [shifted]
      exact Common.Memory.memReadable_sub data.lengthsReadable (8 * index) 8 (by
        have remaining := loop.remaining
        omega)
    stored := ctx.readable state ctx.wf.storedFits
    active := ctx.writable state ctx.wf.chunk.bufferFits (by decide)
    bufferRegister := loop.bufferRegister
    workingPointer := loop.workingPointer
    storedPointer := loop.storedPointer
    direction := state.directionFlag
    separate := clone_separate ctx.wf ctx.stack
    codeApart := by
      intro site member
      exact local_codeApart (site := site) ctx.wf ctx.stack (fun a ha hp => ctx.avoids a ha (.inl hp))
        ctx.code state.loaded ctx.wf.chunk.bufferFits (by
          simp only [List.mem_append] at member ⊢
          simp only [member, true_or])
  }
  have code : CodeIn ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) s :=
    ctx.code.sequence _ (by
      intro site member
      simp only [List.mem_append] at member ⊢
      simp only [member, true_or]) state.loaded
  obtain ⟨fuel, t, run, ready, _, post⟩ := ctx.blocks.load _ s
    (supportedMachine_readyToStep state.machine) code pre
  have frame : MemoryWriteFrame s t (footprint l (l.chunk.sp initial)) :=
    singleton_frame (by simp [footprint]) post.memory
  have stateT := ctx.after_block state run ready post.agrees (by simp) frame
  have dataT := data.of_frame ctx.wf ctx.stack state separation frame
  have tail : (memLoad s.external (l.stored (l.chunk.sp initial) + 63) 8).setWidth 64 =
      BitVec.ofNat 64 ((Wrapper.prefixMessage inputs index).size % 64) := by
    rw [memLoad_8]
    change ((s.external[l.stored (l.chunk.sp initial) + 63]?).getD 0).toBitVec.setWidth 64 = _
    rw [loop.hasher.tailLength]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt8.toNat_ofNat', BitVec.toNat_ofNat]
    have bound := Nat.mod_lt (Wrapper.prefixMessage inputs index).size (by decide : 0 < 64)
    omega
  refine ⟨t, stateT, post, ?_⟩
  refine ⟨post.rip, post.rsp, loop.hasher.of_bytes post.copied, ?_, ?_,
    post.position.trans tail, dataT.bytes ⟨index, loop.remaining⟩,
    dataT.bounded ⟨index, loop.remaining⟩, ?_, post.bufferRegister, ?_⟩
  · rw [post.source, shifted]
    exact data.pointers ⟨index, loop.remaining⟩
  · rw [post.length, shifted]
    exact data.lengths ⟨index, loop.remaining⟩
  · have bound := prefixMessage_size_le inputs (i := index + 1) (j := inputs.size)
      (by have remaining := loop.remaining; omega) (Nat.le_refl _)
    rw [Wrapper.prefixMessage_size, Wrapper.prefixMessage_succ inputs index loop.remaining,
      ByteArray.size_append] at bound
    have total := data.messageBound
    omega
  · intro call member r encoding
    have target := ctx.targets.copies call member
    rw [encoding] at target
    have notSource : ∀ source ∈ l.chunk.bufferSource, r.setWidth 5 ≠ source.setWidth 5 := by
      intro source sourceMember same
      have sameRegister : r = source := by
        apply BitVec.eq_of_toNat_eq
        have numeric := congrArg BitVec.toNat same
        simp only [BitVec.toNat_setWidth] at numeric
        have first := r.isLt
        have second := source.isLt
        omega
      exact ctx.wf.bufferSourceCopies source sourceMember call member r encoding sameRegister.symm
    exact (post.registers (r.setWidth 5) target.2 notSource).trans
      (loop.copyRegister call member r encoding)

end Sha2.Proofs.Common.SHA256.Absorb.Table
