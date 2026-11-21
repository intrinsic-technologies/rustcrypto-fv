import K256.Proofs.Generate.Generator.Multiply.State

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR Common.Field

def squareCopies : Vector (BitVec 64) 5 := #v[0x88, 0x48, 0x50, 0x30, 0x40]

def squareWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 112).toNat, 112⟩, ⟨(sp + 0x30).toNat, 0x28⟩, ⟨(sp + 0x88).toNat, 8⟩,
   ⟨(sp + 0x1bc).toNat, 4⟩, ⟨(sp + 0x490).toNat, 40⟩, ⟨(sp + 0x850).toNat, 40⟩]

def SquarePreparation : Prop :=
  ∀ {fr : Activation} {a : Registers} {m : Ram} {y z : Limbs} {count : BitVec 32},
    let sp := fr.rsp - 0xcb8
    Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d810 fr) →
    SavedWidths a →
    a[1].get 32 = count →
    a[5].get 64 = 0x1000003d10 →
    a[12].get 64 = sp + 0x490 →
    WordsAt m (sp + 0x150) 64 y →
    WordsAt m (sp + 0x178) 64 z →
    ∃ b n, Reaches .l11d810 a m .l11d880 b n ∧
      Atom.All Extracted.programImage b n (Fn11c880.frameAt .l11d880 fr) ∧
      b[5] = ⟨64, 0x1000003d10⟩ ∧
      memLoad n (sp + 0x1bc) 32 = count ∧
      (∀ i : Fin 5, memLoad n (sp + squareCopies[i]) 64 = (squareWords y)[i]) ∧
      WordsAt n (sp + 0x490) 64 (squareWords z) ∧
      RamWriteFrame m n (squareWrites sp)

end K256.Proofs.Generate.Generator.Multiply
