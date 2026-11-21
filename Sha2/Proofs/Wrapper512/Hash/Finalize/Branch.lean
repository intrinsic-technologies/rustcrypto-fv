import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Hash.Finalize.Control
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Wrapper512.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Machine

theorem branch_local [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} (ctx : Context v initial inputs form) (input : Padded v initial s message form)
    :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ AgreesExcept [.flags, .rip] s t ∧ Working v initial t message (compressBlocks v.initialHash message) form ∧
      t.RIP = (if message.size % 128 < 112 then v.pc (lengthOffset v form) form else v.pc (branchOffset v form + 10) form) ∧
      (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 128⟩ : MemoryRegion).HasBytes
        t.external (paddedBuffer message) ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  obtain ⟨t, run, ready, rip, frame⟩ := Control.branch
    (supportedMachine_readyToStep input.machine) input.loaded input.rip
    ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
  have memory := frame.external (by simp [Component.Covers])
  have preserved := Absorb.preserved_of_agrees ctx input.toPreserved run ready frame
    (by simp [Absorb.LocalWrites, Component.Covers]) (by simp)
    (keptOutput := by simp)
    (keptFrameOutput := by intro _; exact .inl (by simp))
  have regs (r : Syntax.Reg) : t.regValue r = s.regValue r := by
    have h := frame.read (n := 64) (r := BitVec.ofNat 5 r.fin.val) (by simp)
    cases r <;> exact h
  refine ⟨t, run, frame, ⟨⟨preserved, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [HashStateAt, memory] using input.hashWords
  · have pointer := input.hashPointer
    cases form <;> simp only [hashPointerState, regs] at pointer ⊢
    all_goals first | exact pointer | (split at pointer ⊢ <;> exact pointer)
  · exact (regs _).trans input.blocks
  · exact (regs _).trans input.blocksHigh
  · exact (regs _).trans input.tailLength
  · rw [rip, input.paddingLength, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 127 - message.size % 128 < 2^64)]
    by_cases small : message.size % 128 < 112
    · simp only [small, ite_true, show ¬ 127 - message.size % 128 < 16 by omega, ite_false]
    · simp only [small, ite_false, show 127 - message.size % 128 < 16 by omega, ite_true]
  · simpa only [memory] using input.bytes

  · exact frame.memoryWriteFrame (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact ha.elim)
  · intro _
    unfold Variant.countValue
    split
    · exact frame.read (by simp)
    · rw [memory]

theorem branch [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} (ctx : Context v initial inputs form) (input : Padded v initial s message form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, Working v initial t message (compressBlocks v.initialHash message) form ∧
      t.RIP = (if message.size % 128 < 112 then v.pc (if form = .slices then 0x32a else 0x243) form else v.pc (if form = .slices then 0x27b else 0x19d) form) ∧
      (⟨(stackPtr initial - 600).toNat, 128⟩ : MemoryRegion).HasBytes
        t.external (paddedBuffer message) := by
  obtain ⟨t, _, _, state, rip, bytes, _, _⟩ := branch_local ctx input
  refine ⟨t, state, ?_, ?_⟩
  · rcases eligible with rfl | rfl <;> exact rip
  · rcases eligible with rfl | rfl <;> exact bytes

end Sha2.Proofs.Wrapper512.Hash.Finalize
