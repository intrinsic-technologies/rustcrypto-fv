import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.State

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

theorem shiftFrame {a c : Registers} {m p : Ram} {sp k off ret : Word} {z : Fin modulus}
    {w : Vector Word 4} {depth : Nat} (h : Entry a m sp z w)
    (frame : RamWriteFrame m p [⟨(sp - 736).toNat, 736⟩])
    (push : k = 8 ∨ k = 24) (room : k.toNat + depth ≤ 328) (slot : off.toNat + 33 ≤ 408)
    (rsp : c[4] = ⟨64, base sp - k⟩) (rdi : c[7] = ⟨64, base sp + off⟩)
    (df : c[22] = ⟨1, 0⟩) (returnAddr : memLoad p (base sp - k) 64 = ret)
    (retLow : ret.toNat < 2^32) :
    CalleeFrame c p (base sp - k) (base sp + off) ret depth 33 := by
  have win := h.stack.of_frame frame
  have lo := h.low
  have hi := h.high
  have align := h.aligned
  have img := Core.stackImage h.stack frame h.image
  refine ⟨rsp, rdi, df, img, ?_, ?_, win.readable.sub ?_ ?_, returnAddr, retLow,
    win.sub ?_ ?_, win.sub ?_ ?_, Or.inr ?_⟩
  all_goals rcases push with rfl|rfl <;> unfold base <;> bv_omega

theorem shiftSource {p : Ram} {sp k dstOff srcOff : Word} {depth : Nat} {x : Int}
    (win : Writable Extracted.programImage p (sp - 736) 736)
    (lo : 736 ≤ sp.toNat) (hi : sp.toNat + 129 ≤ 2^32)
    (kBound : k.toNat ≤ 328) (src : srcOff.toNat + 33 ≤ 408)
    (apart : dstOff.toNat + 33 ≤ srcOff.toNat)
    (value : signedAt p (base sp + srcOff) x) :
    SignedSource p (base sp - k) (base sp + dstOff) (base sp + srcOff) depth 33 x := by
  refine ⟨win.readable.sub ?_ ?_, Or.inr ?_, Or.inr ?_, value⟩
  all_goals unfold base <;> bv_omega

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
