import K256.Proofs.Signing.Composition.Attempt.State

namespace K256.Proofs.Signing.Composition.Attempt.Return

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

structure Constructed (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (r sigS : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+456) (sp s+192) (sp s+192) (sp s+456) where
  output : if r = 0 ∨ sigS = 0 then
    memLoad m (sp s+8) 8 = 1 ∧ memLoad m (sp s+16) 64 = 0
  else
    memLoad m (sp s+8) 8 = 0 ∧ WordsAt m (sp s+16) 64 (Generate.Generator.Multiply.scalarWords r) ∧
      WordsAt m (sp s+48) 64 (Generate.Generator.Multiply.scalarWords sigS)

structure Normalized (s : RamState) (d r sigS : Nat) (a : Registers) (m : Ram) : Prop
    extends CoreMemory s d m where
  rsp : a[4] = ⟨64,sp s⟩
  df : a[22] = ⟨1,0⟩
  first : WordsAt m (sp s+8) 64 (Generate.Generator.Multiply.scalarWords r)
  second : WordsAt m (sp s+40) 64 (Generate.Generator.Multiply.scalarWords
    (if sigS > domain.n / 2 then domain.n - sigS else sigS))

end K256.Proofs.Signing.Composition.Attempt.Return
