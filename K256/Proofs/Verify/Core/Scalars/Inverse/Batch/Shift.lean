import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)

open Generate.Generator.Affine.Invert.Core (LinearArgs)

def ModularShift : Prop := ∀ {a : Registers} {m : Ram} {sp dst ret : Word} {x y : Int}
    {u v : Word} {shift : Nat},
    CalleeFrame a m sp dst ret 304 33 →
    LinearArgs a m sp dst 304 33 x y u v →
    a[9].get 32 = BitVec.ofNat 32 shift → 0 < shift → shift ≤ 62 →
    Readable m (sp + 8) 16 → sp.toNat + 24 ≤ 2^32 →
    (dst.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 24 ≤ dst.toNat) →
    memLoad m (sp + 8) 64 = 0x2021a0 →
    memLoad m (sp + 16) 64 = 0xb4f20099aa774ec1 →
    (x * u.toInt + y * v.toInt).natAbs < 2^shift * domain.n →
    ∃ out r, program.Exec (dialect Extracted.programImage) ⟨⟨.l108980,a,m⟩,[]⟩ out ∧
      CalleeResult a m sp dst ret 304 33 out ∧ signedAt out.store dst r ∧
      r.natAbs < domain.n ∧ ((2 : Int)^shift * r) % domain.n =
        (x * u.toInt + y * v.toInt) % domain.n

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
