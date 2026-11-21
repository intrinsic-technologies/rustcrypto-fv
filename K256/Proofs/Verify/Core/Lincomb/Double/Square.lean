import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Verify.Core.Lincomb.Transfer
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Squares

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR Common.Field
open Generate.Generator.Multiply (SavedWidths)

open Lean Elab Command in
local elab "open_generate_square" : command => do
  let ns := `K256.Proofs.Generate.Generator.Multiply
  let name := mkPrivateNameCore (ns ++ `DoubleExecution.Squares) (ns ++ `squareCall)
  modifyScope fun scope =>
    { scope with openDecls := .explicit `generateSquareCall name :: scope.openDecls }

open_generate_square

set_option maxHeartbeats 700000 in
theorem squareCall {a : Registers} {m : Ram} {sp src dst ret : BitVec 64} {words : Limbs}
    (rsp : a[4] = ⟨64, sp⟩) (rsi : a[6] = ⟨64, src⟩) (rdi : a[7] = ⟨64, dst⟩)
    (df : a[22] = ⟨1, 0⟩) (saved : SavedWidths a)
    (mx : a[39].width = 32) (ft : a[50].width = 16) (fc : a[51].width = 16)
    (win : Writable Extracted.programImage m (sp - 104) 112)
    (source : Readable m src 40) (dest : Writable Extracted.programImage m dst 40)
    (srcAbove : sp.toNat + 8 ≤ src.toNat) (dstAbove : sp.toNat + 8 ≤ dst.toNat)
    (apart : dst.toNat + 40 ≤ src.toNat ∨ src.toNat + 40 ≤ dst.toNat)
    (dstAlign : dst.toNat % 8 = 0) (align : sp.toNat % 16 = 8) (room : 104 ≤ sp.toNat)
    (slot : memLoad m sp 64 = ret) (retLow : ret.toNat < 2^32) (input : WordsAt m src 64 words) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1145f0, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [⟨(sp - 104).toNat, 104⟩, ⟨dst.toNat, 40⟩] ∧
      WordsAt out.store dst 64 (squareWords words) := by
  obtain ⟨out, run, tag, stack, keep, frame, result⟩ :=
    generateSquareCall rsp rsi rdi df saved mx ft fc win source dest srcAbove dstAbove
      apart dstAlign align room slot retLow input
  exact ⟨out, transfer (src := Generate.LIR.Label.l1145f0) (by simp [sharedEntry]) run,
    tag, stack, keep, frame, result⟩

end K256.Proofs.Verify.Core.Lincomb.Double
