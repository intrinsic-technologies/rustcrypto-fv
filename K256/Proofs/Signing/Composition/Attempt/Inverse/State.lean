import K256.Proofs.Signing.Composition.Attempt.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult)

structure DigestReduced (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (a : Registers) (m : Ram) : Prop extends LoopMemory s d msg st m,
    RegistersAt s a (sp s+456) (sp s+192) (sp s+656) (sp s+456) where
  nonce : WordsAt m (sp s+624) 64 (scalarWords k)
  digest : WordsAt m (sp s+656) 64 (scalarWords (digestScalar msg))

structure Entry (a : Registers) (m : Ram) (p : BitVec 64) (k : Nat) : Prop extends
    CalleeFrame a m p (p+16) 0x109db2 736 33 where
  scalarPtr : a[6] = ⟨64,p+728⟩
  modPtr : a[2] = ⟨64,0x2021a0⟩
  invWord : a[1] = ⟨64,0xb4f20099aa774ec1⟩
  onePtr : a[8] = ⟨64,0x202180⟩
  source : Readable m (p+728) 32
  input : WordsAt m (p+728) 64 (scalarWords k)
  high : p.toNat + 760 ≤ 2^32
  positive : 0 < k
  bound : k < domain.n
  slot1Read : Readable m 0x203de0 8
  slot1 : memLoad m 0x203de0 64 = 0x129770
  slot2Read : Readable m 0x203e20 8
  slot2 : memLoad m 0x203e20 64 = 0x100a20
  slotApart : 0x204108 ≤ p.toNat ∨ p.toNat ≤ 0x203de0

def CoreExecution : Prop :=
  ∀ {a m p k}, Entry a m p k → ∃ out,
    LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l108e30,a,m⟩,[]⟩ out ∧
    CalleeResult a m p (p+16) 0x109db2 736 33 out ∧
    WordsAt out.store (p+16) 64 (scalarWords (Curve.inverse domain.n k)) ∧
    memLoad out.store (p+48) 8 = 1 ∧ out.values[9].width = 64

end K256.Proofs.Signing.Composition.Attempt.Inverse
