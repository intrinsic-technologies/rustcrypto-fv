import P256.Proofs.HMAC.Finalize.Padding.Bytes
import P256.Proofs.HMAC.Finalize.Padding.Fill.Call
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

 theorem zero_fill [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Marked initial s message outer) (rip : s.RIP = fillCall outer) :
    ∃ fuel t, Advances boundary fuel s t ∧ Padded initial t message outer ∧
      t.RIP = fillReturn outer ∧
      t.regValue (remainingRegister outer) = BitVec.ofNat 64 (63 - message.size % 64) ∧
      MemoryWriteFrame s t #v[scratchRegion initial] := by
  obtain ⟨u, callRun, _, effect, frame⟩ := fill_call outer pre state.toFrameState rip
  have dst : u.regValue .rdi = stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64 + 1) :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have zero : u.regValue .rsi = 0 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.zero
  have count : u.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64) :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.length
  have callPre := fill_pre pre frame effect.rip dst zero (by
    change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    cases outer
    · exact inProgram_of_textOffset 0xff0 (by decide)
    · exact inProgram_of_textOffset 0x128e (by decide))
  obtain ⟨t, result, zeros, _⟩ := Program.memset_zero_correct callPre
    (by rw [zero]; rfl) count (by omega)
  obtain ⟨fuel, run⟩ := result.execution
  have memory := fill_result_frame pre frame.rsp dst result
  have finalFrame : ScalarFrame.FrameState initial t 0 672 328 :=
    after_result pre (by decide) frame result (scratch_frame memory)
      (result.rsp.trans ((callEffect_stack effect).2.trans state.rsp))
  have saved (r : Syntax.Reg) (member : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = s.regValue r := by
    apply (result.calleeSaved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have bytes (i : Nat) (hi : i < 104) (outside : i ≤ message.size % 64 ∨ 64 ≤ i) :
      t.external[stackPtr initial - 256#64 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 256#64 + BitVec.ofNat 64 i]? :=
    (fill_result_byte pre frame.rsp dst result hi outside).trans
      (call_byte state.toFrameState effect (by decide) (by decide) hi)
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  refine ⟨1 + fuel, t, callRun.trans run, ⟨finalFrame,
    (saved .rbx (by simp)).trans state.outputPointer,
    (saved (positionRegister outer) (by cases outer <;> simp [positionRegister])).trans state.position,
    (saved (countRegister outer) (by cases outer <;> simp [countRegister])).trans state.count,
    (saved (hashRegister outer) (by cases outer <;> simp [hashRegister])).trans state.hashPointer,
    ?_, ?_⟩, result.rip.trans (callEffect_stack effect).1,
    (saved (remainingRegister outer) (by cases outer <;> simp [remainingRegister])).trans state.remaining,
    memoryWriteFrame_trans (call_frame pre state.toFrameState effect) memory⟩
  · apply SHA256.padded_bytes
    · exact hasBytes_copy state.tail (fun i hi => bytes i (by omega) (.inl (by omega)))
    · exact (bytes _ (by omega) (.inl (Nat.le_refl _))).trans state.marker
    · intro i hi
      have h := zeros i hi
      simpa only [dst, BitVec.add_assoc, ← BitVec.ofNat_add] using h
  · apply state.hash.copy
    intro i hi
    have h := bytes (64 + i) (by omega) (.inr (by omega))
    have address : stackPtr initial - 256#64 + 64#64 = stackPtr initial - 192#64 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, address] using h

 theorem finish_fill [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Marked initial s message outer) (rip : s.RIP = fillCall outer)
    (small : message.size % 64 < 56) :
    ∃ fuel t, Advances boundary fuel s t ∧ Padded initial t message outer ∧
      t.RIP = lengthStart outer ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  obtain ⟨fuel, u, run, padded, atBranch, remaining, memory⟩ := zero_fill outer pre state rip
  let modrm : UInt8 := if outer then 0xff else 0xfc
  have target : fillReturn outer + 174#64 = lengthStart outer := by cases outer <;> rfl
  have code : CodeIn (codeRange (fillReturn outer) [0x49,0x83,modrm,7,0x0f,0x87,0xa4,0,0,0]) u := by
    cases outer
    · exact programText_slice (programLoaded_codeIn padded.loaded) 0xff0 _ (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn padded.loaded) 0x128e _ (by decide) (by decide +kernel)
  have large : 8 ≤ ((Operand.reg (gprNumber 0 1 (modrmRm modrm)) : Operand 64).read u).toNat := by
    have eq : ((Operand.reg (gprNumber 0 1 (modrmRm modrm)) : Operand 64).read u) =
        u.regValue (remainingRegister outer) := by
      have reg : gprNumber 0 1 (modrmRm modrm) = (if outer then 15 else 12) := by
        cases outer <;> decide +kernel
      rw [reg]
      cases outer <;> rfl
    rw [eq, remaining, BitVec.toNat_ofNat]
    omega
  obtain ⟨t, branch, ready, atLength, agrees⟩ := padding_branch (fillReturn outer) modrm
    (by cases outer <;> decide) (by cases outer <;> decide)
    (readyToStep padded.machine padded.bindingsSupported) code atBranch large
    (by cases outer
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xff4 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1292 (by decide)))
    (by rw [target]; cases outer
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x109e (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x133c (by decide)))
    (by cases outer <;> decide)
  have external := agrees.external (by simp [Component.Covers])
  have finalFrame := padded.toFrameState.after_registers ready agrees
    (by simp [Component.Covers]) (by simp)
  have registers (r : Syntax.Reg) : t.regValue r = u.regValue r := by
    cases r
    · exact agrees.read (n := 64) (r := 0) (by simp)
    · exact agrees.read (n := 64) (r := 1) (by simp)
    · exact agrees.read (n := 64) (r := 2) (by simp)
    · exact agrees.read (n := 64) (r := 3) (by simp)
    · exact agrees.read (n := 64) (r := 4) (by simp)
    · exact agrees.read (n := 64) (r := 5) (by simp)
    · exact agrees.read (n := 64) (r := 6) (by simp)
    · exact agrees.read (n := 64) (r := 7) (by simp)
    · exact agrees.read (n := 64) (r := 8) (by simp)
    · exact agrees.read (n := 64) (r := 9) (by simp)
    · exact agrees.read (n := 64) (r := 10) (by simp)
    · exact agrees.read (n := 64) (r := 11) (by simp)
    · exact agrees.read (n := 64) (r := 12) (by simp)
    · exact agrees.read (n := 64) (r := 13) (by simp)
    · exact agrees.read (n := 64) (r := 14) (by simp)
    · exact agrees.read (n := 64) (r := 15) (by simp)
  refine ⟨fuel + 2, t, run.trans branch, ⟨finalFrame,
    (registers _).trans padded.outputPointer, (registers _).trans padded.position,
    (registers _).trans padded.count, (registers _).trans padded.hashPointer, ?_, ?_⟩,
    atLength.trans target, ?_⟩
  · simpa only [MemoryRegion.HasBytes, external] using padded.buffer
  · simpa only [SHA256.HashStateAt, external] using padded.hash
  · intro a ha
    rw [external]
    exact memory a ha

end P256.Proofs.HMAC.Finalize.Padding
