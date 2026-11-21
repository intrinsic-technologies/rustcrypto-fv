import P256.Proofs.Sec1.Affine.Compressed.Prepare
import P256.Proofs.Sec1.Affine.Compressed.Call
import P256.Proofs.Sec1.Affine.Compressed.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {tag : UInt8} (pre : AffineDecodePre s boundary bytes) (state : Routed s t tag)
    (size : bytes.size = 33) (tagByte : bytes.data[0]? = some tag)
    (valid : tag = 2 ∨ tag = 3)
    (routine : ∀ v, Decompress.Pre v boundary (bytes.extract 1 33) (tag == 3) →
      ∃ u, CalleeResult v u boundary 80 2592 ∧
        AffineResultAt u (v.regValue .rdi) (P256.Spec.Points.decompress
          (P256.Spec.Points.element bytes 1) (tag == 3)))
    (rip : t.RIP = 0x110108) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110128 ∧
      AffineResultAt u (stackPtr s - 592) (P256.Spec.Points.decodePoint bytes) ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .r15 = stackPtr s - 592 := by
  obtain ⟨n, v, runV, stateV, ipV, input, output, parity, dest, buffer⟩ :=
    prepare pre state valid rip
  obtain ⟨m, u, runU, stateU, ipU, decoded, saved⟩ :=
    decompression_call pre size stateV routine 0x10123 0xfffffad8 (by decide)
      (by decide +kernel) (by decide) (offset := 592) (by decide) (by decide)
      ipV input output parity
  refine ⟨n + m, u, runV.trans runU, stateU, ipU, ?_,
    (saved .rbx (by simp)).trans dest, (saved .r15 (by simp)).trans buffer⟩
  rwa [decodePoint_eq_decompress size tagByte valid]

end P256.Proofs.Sec1.Affine.Compressed
