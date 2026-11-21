import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix
import P256.Proofs.Nonce.Update.Seeded.Absorb.Cross
import P256.Proofs.Nonce.Update.Seeded.Absorb.Short

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem absorb [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced : ByteArray}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (prepared : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Absorbed initial t state (secret ++ reduced) := by
  obtain ⟨secretPointer,reducedPointer,secretPtr,secretLen,reducedPtr,reducedLen,emptyLen,secretSeed,reducedSeed⟩ := pre.seeds
  have headSize : (state.value ++ (⟨#[1]⟩ : ByteArray)).size = 33 := by
    rw [ByteArray.size_append,prepared.drbg.value_size]
    rfl
  obtain ⟨f1,s1,r1,h1⟩ := Absorb.«prefix» pre.toDrbgCalleePre prepared
  obtain ⟨f2,s2,r2,h2⟩ := Absorb.cross pre h1 headSize secretPtr secretLen secretSeed
  obtain ⟨f3,s3,r3,h3⟩ := Absorb.short (added := reduced) pre h2 (by decide)
    (by simpa only [Nat.mul_one,BitVec.ofNat_eq_ofNat] using reducedPtr)
    (by simpa only [pre.reducedSize,Nat.mul_one,Nat.reduceAdd,BitVec.ofNat_eq_ofNat] using reducedLen)
    (by rw [ByteArray.size_append,headSize,pre.secretSize,pre.reducedSize]; decide)
    (.inl reducedSeed)
  have loop : Absorb.Loop initial s3 state ((state.value ++ ⟨#[1]⟩) ++ secret ++ reduced) 2 :=
    ⟨h3.toContext,h3.rip,h3.current,h3.hashPointer,h3.copyPointer,h3.hmac⟩
  let emptyPointer := memLoad s3.external (initial.regValue .rsi + 32) 64
  have readable : MemReadable s3 (initial.regValue .rsi + 32) 8 :=
    Update.Absorb.descriptor_readable pre loop.toFrameState (by decide : 32+8≤48)
  have currentPointer : loadBytes s3.external (initial.regValue .rsi + 32) 8 = .ok emptyPointer :=
    (Bytes.of_memLoad (n:=64) readable.mem).loadBytes64
  have pointer : loadBytes initial.external (initial.regValue .rsi + 32) 8 = .ok emptyPointer := by
    apply P256.Proofs.Program.loadBytes_ok_copy _ currentPointer
    intro i hi
    have h := Update.Absorb.descriptor_bytes pre loop.toFrameState (32+i) (by omega)
    have eq : initial.regValue .rsi + BitVec.ofNat 64 (32+i) = initial.regValue .rsi + 32 + BitVec.ofNat 64 i := by bv_omega
    rw [eq] at h
    exact h.symm
  obtain ⟨f4,t,r4,h4⟩ := Absorb.short (added := ByteArray.empty) pre loop (by decide)
    (by simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat] using pointer)
    (by simpa only [ByteArray.size_empty,Nat.reduceMul,Nat.reduceAdd,BitVec.ofNat_eq_ofNat] using emptyLen)
    (by simp only [ByteArray.size_empty,Nat.add_zero]; omega)
    (.inr rfl)
  refine ⟨f1+f2+f3+f4,t,((r1.trans r2).trans r3).trans r4,
    h4.toFrameState,h4.rip,h4.drbg,?_,h4.savedPointer⟩
  simpa only [ByteArray.append_empty,ByteArray.append_assoc] using h4.hmac

end P256.Proofs.Nonce.Update.Seeded
