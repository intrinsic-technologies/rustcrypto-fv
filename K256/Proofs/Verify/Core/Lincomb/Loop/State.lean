import K256.Proofs.Verify.Core.Lincomb.Loop.Accumulator

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)

abbrev baseSp (sp : BitVec 64) := sp - 0x1d8

structure SavedFrame (initial : Registers) (original : Ram) (sp dst : BitVec 64)
    (a : Registers) (m : Ram) : Prop where
  rsp : a[4] = ⟨64, baseSp sp⟩
  dest : memLoad m (baseSp sp + 0xd0) 64 = dst
  rbx : memLoad m (sp - 48) 64 = initial[3].get 64
  r12 : memLoad m (sp - 40) 64 = initial[12].get 64
  r13 : memLoad m (sp - 32) 64 = initial[13].get 64
  r14 : memLoad m (sp - 24) 64 = initial[14].get 64
  r15 : memLoad m (sp - 16) 64 = initial[15].get 64
  rbp : memLoad m (sp - 8) 64 = initial[5].get 64
  control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → a[i] = initial[i]
  frame : RamWriteFrame original m [scratch sp 0x478]

structure RoundState (initial : Registers) (original : Ram) (sp dst dataPtr : BitVec 64)
    (bases : Fin 4 → Curve.Point) (ds : Fin 4 → List Int) (k : Nat)
    (a : Registers) (m : Ram) : Prop extends SavedFrame initial original sp dst a m where
  counter : a[9].get 64 = BitVec.ofNat 64 k
  front : a[13].get 64 = 0
  nextTable : a[14].get 64 = dataPtr
  tableEnd : a[5] = ⟨64, dataPtr + 0x1340⟩
  back : a[8] = ⟨64, 0⟩
  savedFront : memLoad m (baseSp sp + 0x40) 64 = 0
  savedNext : memLoad m (baseSp sp + 0x38) 64 = dataPtr
  savedBack : memLoad m (baseSp sp) 64 = 0
  point : ∃ q : Projective, q.Stored m (baseSp sp + 0x130) ∧ q.valid ∧ q.value = suffix bases ds k
  inactive : (memLoad m (baseSp sp + 0x28) 8 &&& 1) = 0 → suffix bases ds k = .infinity

end K256.Proofs.Verify.Core.Lincomb.Loop
