import P256.Proofs.Sec1.Affine.Compressed.Input
import P256.Proofs.Program.FieldCall.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decompression_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : AffineDecodePre s boundary bytes)
    (size : bytes.size = 33) (state : Frame s t)
    (routine : ∀ v, Decompress.Pre v boundary (bytes.extract 1 33) odd →
      ∃ u, CalleeResult v u boundary 80 2592 ∧
        AffineResultAt u (v.regValue .rdi) (P256.Spec.Points.decompress
          (P256.Spec.Points.element bytes 1) odd))
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5
      (disp.signExtend 64) = 0x10fc00)
    {offset : Nat} (above : offset + 8 ≤ 768) (saved : 80 + 48 ≤ offset)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset) (input : t.regValue .rsi = s.regValue .rsi + 1)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 offset)
    (parity : t.regValue .rdx = BitVec.ofNat 64 odd.toNat) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      AffineResultAt u (stackPtr s - BitVec.ofNat 64 offset)
        (P256.Spec.Points.decompress (P256.Spec.Points.element bytes 1) odd) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = t.regValue r) := by
  obtain ⟨v, runV, readyV, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (frameOffset := 760) (by decide) (by decide) state codeOffset disp
    (by omega) codeBytes (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0xfc00 (by decide)) rip
  let retAddress := Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64)
  change (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    5 (disp.signExtend 64)) retAddress t).Holds t v at effect
  rw [target] at effect
  have frameV := state.after_call pre.toCalleePre (by decide) (by decide) readyV effect
  have vin : v.regValue .rsi = s.regValue .rsi + 1 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input
  have vout : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 offset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans output
  have vpar : v.regValue .rdx = BitVec.ofNat 64 odd.toNat :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans parity
  have ret : (returnBoundary v).rip = retAddress := (callEffect_stack effect).1
  have cp := decompression_pre pre size frameV effect.rip vin (offset := offset)
    above (by omega) vout vpar (by
      rw [ret]
      simpa only [retAddress, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        inProgram_of_textOffset (codeOffset + 5) codeBound)
  obtain ⟨u, result, decoded⟩ := routine v cp
  have memory := FieldCall.stack_result_work_frame pre.toCalleePre frameV result vout
    (by omega) saved (by decide) (by decide)
  obtain ⟨fuel, runU⟩ := result.execution
  refine ⟨1 + fuel, u, runV.trans runU,
    FieldCall.after_result pre.toCalleePre frameV result (by decide) memory,
    result.rip.trans ret, ?_, ?_⟩
  · rwa [vout] at decoded
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Sec1.Affine.Compressed
