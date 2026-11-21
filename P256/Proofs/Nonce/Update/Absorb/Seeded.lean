import P256.Proofs.Nonce.Update.Absorb.Seeded.Enter
import P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderPrepare
import P256.Proofs.Nonce.Update.Absorb.Seeded.CrossFinish
import P256.Proofs.Nonce.Update.Absorb.Seeded.Short

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

set_option maxHeartbeats 1000000 in
theorem seeded [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced : ByteArray}
    (pre : UpdateSeededPre initial boundary state secret reduced) (tagged : Tagged initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Absorbed initial t state (.seeded secret reduced) := by
  obtain ⟨secretPointer,reducedPointer,secretPtr,secretLen,reducedPtr,reducedLen,emptyLen,secretSeed,reducedSeed⟩ := pre.seeds
  have headSize : (state.value ++ (⟨#[0]⟩ : ByteArray)).size = 33 := by
    rw [ByteArray.size_append,pre.stateBytes.value_size]
    rfl
  obtain ⟨f1,s1,r1,h1⟩ := Seeded.enter pre tagged
  obtain ⟨f2,s2,r2,h2⟩ := Seeded.read (len := 32) pre h1 (by decide)
    (by simpa only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using secretPtr)
    (by simpa only [Nat.mul_zero,Nat.zero_add,BitVec.ofNat_eq_ofNat] using secretLen)
  obtain ⟨f3,s3,r3,h3⟩ := Seeded.prepare_cross pre.toDrbgCalleePre h2 headSize
  obtain ⟨f4,s4,r4,h4⟩ := Seeded.copy_cross pre.toDrbgCalleePre h3 headSize pre.secretSize secretSeed
  obtain ⟨f5,s5,r5,h5⟩ := Seeded.compress pre.toDrbgCalleePre h4
  obtain ⟨f6,s6,r6,h6⟩ := Seeded.prepare_remainder pre.toDrbgCalleePre h5
  obtain ⟨f7,s7,r7,h7⟩ := Seeded.copy_remainder pre.toDrbgCalleePre h6 headSize pre.secretSize secretSeed
  obtain ⟨f8,s8,r8,h8⟩ := Seeded.finish_cross pre h7
  obtain ⟨f9,s9,r9,h9⟩ := Seeded.short (added := reduced) pre h8 (by decide)
    (by simpa only [Nat.mul_one,BitVec.ofNat_eq_ofNat] using reducedPtr)
    (by simpa only [pre.reducedSize,Nat.mul_one,Nat.reduceAdd,BitVec.ofNat_eq_ofNat] using reducedLen)
    (by rw [ByteArray.size_append,headSize,pre.secretSize,pre.reducedSize]; decide)
    (.inl reducedSeed)
  have loop : Seeded.Loop initial s9 state ((state.value ++ ⟨#[0]⟩) ++ secret ++ reduced) 2 :=
    ⟨h9.toContext,h9.rip,h9.current,h9.hmac⟩
  let emptyPointer := memLoad s9.external (initial.regValue .rsi + 32) 64
  have readable : MemReadable s9 (initial.regValue .rsi + 32) 8 :=
    descriptor_readable pre loop.toFrameState (by decide : 32+8≤48)
  have currentPointer : loadBytes s9.external (initial.regValue .rsi + 32) 8 = .ok emptyPointer :=
    (Bytes.of_memLoad (n:=64) readable.mem).loadBytes64
  have pointer : loadBytes initial.external (initial.regValue .rsi + 32) 8 = .ok emptyPointer := by
    apply P256.Proofs.Program.loadBytes_ok_copy _ currentPointer
    intro i hi
    have h := descriptor_bytes pre loop.toFrameState (32+i) (by omega)
    have eq : initial.regValue .rsi + BitVec.ofNat 64 (32+i) = initial.regValue .rsi + 32 + BitVec.ofNat 64 i := by bv_omega
    rw [eq] at h
    exact h.symm
  obtain ⟨f10,t,r10,h10⟩ := Seeded.short (added := ByteArray.empty) pre loop (by decide)
    (by simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat] using pointer)
    (by simpa only [ByteArray.size_empty,Nat.reduceMul,Nat.reduceAdd,BitVec.ofNat_eq_ofNat] using emptyLen)
    (by simp only [ByteArray.size_empty,Nat.add_zero]; omega)
    (.inr rfl)
  refine ⟨f1+f2+f3+f4+f5+f6+f7+f8+f9+f10,t,
    ((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans r10,
    h10.toFrameState,h10.rip,h10.drbg,?_,h10.savedPointer,h10.savedValue,h10.savedCount,h10.descriptors,h10.savedEnd⟩
  simpa only [ByteArray.append_empty,UpdateInput.seed,ByteArray.append_assoc] using h10.hmac

end P256.Proofs.Nonce.Update.Absorb
