import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

def digitWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp + 0x58).toNat,120⟩, ⟨(sp + 0xe0).toNat,80⟩]

structure Packed (sp : BitVec 64) (q : Projective) (a b : Registers) (m n : Ram) : Prop where
  keep : ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i]
  dst : b[7] = ⟨64,sp + 0x130⟩
  src : b[6] = ⟨64,sp + 0x58⟩
  arguments : ParseSignature.ArgumentWidths b
  point : q.Stored n (sp + 0x58)
  frame : RamWriteFrame m n (digitWrites sp)

end K256.Proofs.Verify.Core.Lincomb.Loop
