import P256.Proofs.Sec1.Affine.Compact.Prepare
import P256.Proofs.Sec1.Affine.Compressed.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Routed s t 5)
    (size : bytes.size = 33)
    (routine : ∀ v, Decompress.Pre v boundary (bytes.extract 1 33) false →
      ∃ u, CalleeResult v u boundary 80 2592 ∧
        AffineResultAt u (v.regValue .rdi) (P256.Spec.Points.decompress
          (P256.Spec.Points.element bytes 1) false))
    (rip : t.RIP = 0x11020f) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11022c ∧
      AffineResultAt u (stackPtr s - 744) (P256.Spec.Points.decompress (P256.Spec.Points.element bytes 1) false) ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .r15 = stackPtr s - 744 ∧ u.regValue .r13 = 0 := by
  obtain ⟨n, v, runV, stateV, ipV, input, output, parity, dest, buffer, zero⟩ :=
    prepare pre state rip
  obtain ⟨m, u, runU, stateU, ipU, decoded, saved⟩ :=
    Compressed.decompression_call pre size stateV routine 0x10227 0xfffff9d4 (by decide)
      (by decide +kernel) (by decide) (offset := 744) (by decide) (by decide)
      ipV input output parity
  exact ⟨n + m, u, runV.trans runU, stateU, ipU, decoded,
    (saved .rbx (by simp)).trans dest, (saved .r15 (by simp)).trans buffer,
    (saved .r13 (by simp)).trans zero⟩

end P256.Proofs.Sec1.Affine.Compact
