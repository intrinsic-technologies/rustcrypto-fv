import K256.Proofs.Verify.Core.Lincomb.Loop.State

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)

abbrev row (table : BitVec 64) (j : Fin 4) :=
  if j.val < 2 then table else table + 0x9a0

structure Column (initial : Registers) (original : Ram) (sp dst table : BitVec 64)
    (k : Nat) (value : Curve.Point) (a : Registers) (m : Ram) : Prop
    extends SavedFrame initial original sp dst a m where
  last : a[5] = ⟨64,table + 0x1340⟩
  back : a[8] = ⟨64,0⟩
  counter : a[9] = ⟨64,BitVec.ofNat 64 k⟩
  savedCounter : memLoad m (baseSp sp + 0x10) 64 = BitVec.ofNat 64 k
  savedFront : memLoad m (baseSp sp + 0x40) 64 = 0
  savedNext : memLoad m (baseSp sp + 0x38) 64 = table
  savedBack : memLoad m (baseSp sp) 64 = 0
  point : ∃ q : Projective, q.Stored m (baseSp sp + 0x130) ∧ q.valid ∧ q.value = value
  inactive : (memLoad m (baseSp sp + 0x28) 8 &&& 1) = 0 → value = .infinity

structure Cursor (sp table : BitVec 64) (j : Fin 4) (index : Nat)
    (a : Registers) (m : Ram) : Prop where
  count : a[3] = ⟨64,2⟩
  component : a[12] = ⟨64,BitVec.ofNat 64 index⟩
  base : a[13] = ⟨64,row table j⟩
  next : a[14] = ⟨64,row table j + 0x9a0⟩
  digits : memLoad m (baseSp sp + 0x18) 64 = row table j + 0x780

end K256.Proofs.Verify.Core.Lincomb.Loop
