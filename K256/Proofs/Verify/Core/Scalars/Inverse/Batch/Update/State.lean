import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.State
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Shift
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Registers

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)

open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

abbrev Controls (b c : Registers) := ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]

def linearWrites (sp : Word) : List MemoryRegion :=
  [⟨(sp - 720).toNat,336⟩, ⟨(base sp + 176).toNat,80⟩, ⟨(base sp + 304).toNat,40⟩]

def modularWrites (sp : Word) : List MemoryRegion :=
  [⟨(sp - 720).toNat,416⟩, ⟨(base sp + 176).toNat,80⟩, ⟨(base sp + 304).toNat,40⟩]

structure LinearRows (b : Registers) (p : Ram) (sp : Word) (s n : Nat)
    (w : Words) (c : Registers) (q : Ram) : Prop where
  rsp : c[4] = ⟨64, base sp⟩
  shift : c[5] = ⟨64, BitVec.ofNat 64 (count n)⟩
  rows : Rows c w
  controls : Controls b c
  remaining : memLoad q (base sp + 336) 64 = BitVec.ofNat 64 (591-n)
  fValue : signedAt q (base sp + 176) (Inverse.model s (n + count n)).f
  gValue : signedAt q (base sp + 216) (Inverse.model s (n + count n)).g
  frame : RamWriteFrame p q (linearWrites sp)

structure ModularRows (b : Registers) (p : Ram) (sp : Word) (s n : Nat)
    (w : Words) (c : Registers) (q : Ram) (d e : Int) : Prop where
  rsp : c[4] = ⟨64, base sp - 16⟩
  shift : c[5] = ⟨64, BitVec.ofNat 64 (count n)⟩
  delta : c[12] = ⟨64, w.delta⟩
  controls : Controls b c
  remaining : memLoad q (base sp + 336) 64 = BitVec.ofNat 64 (591-n)
  fValue : signedAt q (base sp + 8) (Inverse.model s (n + count n)).f
  gValue : signedAt q (base sp + 48) (Inverse.model s (n + count n)).g
  dValue : signedAt q (base sp + 176) d
  eValue : signedAt q (base sp + 216) e
  frame : RamWriteFrame p q (modularWrites sp)

theorem shiftFrame {a c : Registers} {m p : Ram} {sp k off ret : Word} {s : Nat}
    {depth : Nat} (h : Entry a m sp s)
    (frame : RamWriteFrame m p [⟨(sp - 720).toNat, 720⟩])
    (push : k = 8 ∨ k = 24) (room : k.toNat + depth ≤ 328) (slot : off.toNat + 33 ≤ 392)
    (rsp : c[4] = ⟨64, base sp - k⟩) (rdi : c[7] = ⟨64, base sp + off⟩)
    (df : c[22] = ⟨1, 0⟩) (returnAddr : memLoad p (base sp - k) 64 = ret)
    (retLow : ret.toNat < 2^32) :
    CalleeFrame c p (base sp - k) (base sp + off) ret depth 33 := by
  have win := h.stack.of_frame frame
  have lo := h.depthBound
  have hi := h.high
  have align := h.aligned
  have img := Generate.Generator.Affine.Invert.Core.stackImage h.stack frame h.image
  refine ⟨rsp, rdi, df, img, ?_, ?_, win.readable.sub ?_ ?_, returnAddr, retLow,
    win.sub ?_ ?_, win.sub ?_ ?_, Or.inr ?_⟩
  all_goals rcases push with rfl|rfl <;> unfold base <;> bv_omega

theorem shiftSource {p : Ram} {sp k dstOff srcOff : Word} {depth : Nat} {x : Int}
    (win : Writable Extracted.programImage p (sp - 720) 720)
    (lo : 720 ≤ sp.toNat) (hi : sp.toNat + 360 ≤ 2^32)
    (kBound : k.toNat ≤ 328) (src : srcOff.toNat + 33 ≤ 392)
    (apart : srcOff.toNat + 33 ≤ dstOff.toNat)
    (dst : dstOff.toNat + 33 ≤ 392) (value : signedAt p (base sp + srcOff) x) :
    Generate.Generator.Affine.Invert.Core.SignedSource p (base sp - k) (base sp + dstOff) (base sp + srcOff) depth 33 x := by
  refine ⟨win.readable.sub ?_ ?_, Or.inr ?_, Or.inl ?_, value⟩
  all_goals unfold base <;> bv_omega

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
