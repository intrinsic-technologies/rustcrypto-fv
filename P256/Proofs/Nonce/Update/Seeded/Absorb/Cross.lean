import P256.Proofs.Nonce.Update.Seeded.Absorb.CrossFinish
import P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderPrepare

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem cross [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced input : ByteArray} {address : BitVec 64}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (loop : Loop initial s state input 0) (inputSize : input.size = 33)
    (pointer : loadBytes initial.external (initial.regValue .rsi) 8 = .ok address)
    (length : loadBytes initial.external (initial.regValue .rsi + 8) 8 = .ok (32 : BitVec 64))
    (seed : UpdateSeedAt initial address secret) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t state (input ++ secret) 1 := by
  obtain ⟨f1,s1,r1,h1⟩ := read pre loop (by decide) (by simpa only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using pointer) length
  obtain ⟨f2,s2,r2,h2⟩ := prepare_cross pre.toDrbgCalleePre h1 inputSize
  obtain ⟨f3,s3,r3,h3⟩ := copy_cross pre.toDrbgCalleePre h2 inputSize pre.secretSize seed
  obtain ⟨f4,s4,r4,h4⟩ := compress pre.toDrbgCalleePre h3
  obtain ⟨f5,s5,r5,h5⟩ := prepare_remainder pre.toDrbgCalleePre h4
  obtain ⟨f6,s6,r6,h6⟩ := copy_remainder pre.toDrbgCalleePre h5 inputSize pre.secretSize seed
  obtain ⟨f7,s7,r7,h7⟩ := finish_cross pre h6
  exact ⟨f1+f2+f3+f4+f5+f6+f7,s7,(((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7,h7⟩

end P256.Proofs.Nonce.Update.Seeded.Absorb
