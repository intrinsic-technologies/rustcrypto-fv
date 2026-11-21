import K256.Proofs.Signing.Composition.Attempt.Inverse.LoopState
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Frame

namespace K256.Proofs.Signing.Composition.Attempt.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Affine.Invert
open Generate.Generator.Affine.Invert.Core (base signedAt roundsBefore batchLabel CalleeFrame)
open Generate.Generator.Affine.Invert.Core.Batch (count Inner Rows Controls setupWrites linearWrites modularWrites)
open Verify.Core (Registers)
open Standards.SECG.DomainParameters.Secp256k1
open SafeGcd.Batch (Words)

open Lean Elab Command in
scoped elab "open_order_batch " path:ident " (" decls:ident+ ")" : command => do
  let ns := `K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
  for decl in decls do
    let name := mkPrivateNameCore (ns ++ path.getId) (ns ++ decl.getId)
    modifyScope fun scope => { scope with openDecls := .explicit decl.getId name :: scope.openDecls }

structure LinearRows (b : Registers) (p : Ram) (sp : Word) (z : Nat) (j : Nat)
    (s : Words) (c : Registers) (q : Ram) : Prop where
  rsp : c[4] = ⟨64, base sp⟩
  delta : c[5] = ⟨64, s.delta⟩
  second : c[12] = ⟨64, base sp + 56⟩
  shift : c[14] = ⟨64, BitVec.ofNat 64 (count j)⟩
  u : c[15] = ⟨64, s.u⟩
  v : c[3] = ⟨64, s.v⟩
  qWord : memLoad q (base sp + 8) 64 = s.q
  rWord : memLoad q (base sp + 104) 64 = s.r
  remaining : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j)
  firstResult : signedAt q (base sp + 16) (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).f
  secondResult : signedAt q (base sp + 56) (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).g
  controls : Controls b c
  frame : RamWriteFrame p q (linearWrites sp)

structure ModularRows (b : Registers) (p : Ram) (sp : Word) (z : Nat) (j : Nat)
    (s : Words) (c : Registers) (q : Ram) (d' e' : Int) : Prop where
  rsp : c[4] = ⟨64, base sp - 16⟩
  delta : c[5] = ⟨64, s.delta⟩
  second : c[12] = ⟨64, base sp + 56⟩
  scratch : c[14] = ⟨64, base sp + 16⟩
  shift : c[15] = ⟨64, BitVec.ofNat 64 (count j)⟩
  remaining : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j)
  fValue : signedAt q (base sp + 120) (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).f
  gValue : signedAt q (base sp + 168) (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).g
  firstResult : signedAt q (base sp + 16) d'
  secondResult : signedAt q (base sp + 56) e'
  controls : Controls b c
  frame : RamWriteFrame p q (modularWrites sp)

theorem shiftFrame {a c : Registers} {m p : Ram} {sp k off ret : Word} {z : Nat}
    {depth : Nat} (h : Entry a m sp z)
    (frame : RamWriteFrame m p [⟨(sp - 736).toNat, 736⟩])
    (push : k = 8 ∨ k = 24) (room : k.toNat + depth ≤ 328) (slot : off.toNat + 33 ≤ 408)
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

end K256.Proofs.Signing.Composition.Attempt.Inverse.Batch
