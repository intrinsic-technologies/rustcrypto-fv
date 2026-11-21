import P256.Proofs.Nonce.Update.Absorb.Seeded.ShortFinish

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced input added : ByteArray} {index : Nat} {address : BitVec 64}
    (pre : UpdateSeededPre initial boundary state secret reduced)
    (loop : Loop initial s state input index) (indexBound : index < 3)
    (pointer : loadBytes initial.external (initial.regValue .rsi + BitVec.ofNat 64 (16*index)) 8 = .ok address)
    (length : loadBytes initial.external (initial.regValue .rsi + BitVec.ofNat 64 (16*index+8)) 8 = .ok (BitVec.ofNat 64 added.size))
    (fits : input.size % 64 + added.size < 64)
    (source : UpdateSeedAt initial address added ∨ added = ByteArray.empty) :
    ∃ fuel t, Advances boundary fuel s t ∧ Finished initial t state (input ++ added) index := by
  obtain ⟨f1,s1,r1,h1⟩ := read pre loop indexBound pointer length
  obtain ⟨f2,s2,r2,h2⟩ := prepare_short pre.toDrbgCalleePre h1 fits
  obtain ⟨f3,s3,r3,h3⟩ := copy_short pre.toDrbgCalleePre h2 fits source
  obtain ⟨f4,s4,r4,h4⟩ := finish_short pre h3 fits indexBound
  exact ⟨f1+f2+f3+f4,s4,((r1.trans r2).trans r3).trans r4,h4⟩

end P256.Proofs.Nonce.Update.Absorb.Seeded
