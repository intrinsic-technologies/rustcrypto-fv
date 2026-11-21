import P256.Proofs.Nonce.Update.Seeded.Absorb.ShortPrepare
import P256.Proofs.Nonce.Update.Seeded.Absorb.Memory
import P256.Proofs.Nonce.Update.Seeded.Absorb.SeedCopy
import P256.Proofs.Nonce.Update.Absorb.ZeroCopy
import P256.Proofs.Nonce.Update.Absorb.HmacUsed

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb
open Update.Absorb.Seeded (copy_scratch_byte)

structure ShortCopied [Bindings] (initial s : RamState) (state : State) (input added : ByteArray)
    (index : Nat) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a76c
  current : s.regValue .rbp = initial.regValue .rsi + BitVec.ofNat 64 (16 * index)
  copyPointer : s.regValue .r13 = 0x11c930
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key input
  buffer : (MemoryRegion.mk (scratch initial + 320).toNat (input.size % 64 + added.size)).HasBytes
    s.external (SHA256.remainderBytes input ++ added)
  position : s.regValue .r14 = BitVec.ofNat 64 (input.size % 64)
  length : s.regValue .rbx = BitVec.ofNat 64 added.size

set_option maxHeartbeats 1000000 in
theorem copy_short [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input added : ByteArray} {index : Nat} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (ready : ShortReady initial s state input index address added.size)
    (short : input.size % 64 + added.size < 64)
    (source : UpdateSeedAt initial address added ∨ added = ByteArray.empty) :
    ∃ fuel t, Advances boundary fuel s t ∧ ShortCopied initial t state input added index := by
  have destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (360 - input.size % 64) := by
    rw [ready.destination]
    simp only [scratch]
    bv_omega
  have access : added.size = 0 ∨ ∃ inputBytes : ByteArray, UpdateSeedAt initial address inputBytes ∧
      0 + added.size ≤ inputBytes.size := by
    rcases source with seed | empty
    · exact Or.inr ⟨added, seed, by omega⟩
    · exact Or.inl (by rw [empty]; rfl)
  have copy : ∃ t, SeedCopyResult initial s t boundary added.size (360 - input.size % 64) 0x10a76c address := by
    obtain ⟨t,result⟩ := Seeded.Absorb.copy_seed (sourceOffset := 0) (count := added.size)
      pre ready.toFrameState access (by omega) (by omega) (by omega) 0xa769
      (by decide) (by decide +kernel) ready.copyPointer ready.rip
      (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using ready.source) destination ready.count
    exact ⟨t,by simpa only [Extracted.textAddress,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.reduceAdd] using result⟩
  obtain ⟨t,result⟩ := copy
  have ctx := ready.toContext.after_copy pre result (by omega)
  have old : HMAC.HmacStateAt t (scratch initial + 256) state.key input := by
    apply hmacStateAt_copy_used ready.hmac
    intro i hi used
    have h := copy_scratch_byte (offset := 256+i) (len := 1) pre result (by omega) (by omega) (by omega)
      (by rcases used with left | right <;> omega) (i:=0) (by decide)
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.add_zero] using h
  have oldBuffer : (MemoryRegion.mk (scratch initial + 320).toNat (input.size % 64)).HasBytes
      t.external (SHA256.remainderBytes input) := by
    have rem : (HMAC.keyPad state.key 0x36 ++ input).size % 64 = input.size % 64 := by
      rw [ByteArray.size_append,HMAC.keyPad_size]; omega
    simpa only [rem,HMAC.remainderBytes_keyPad_append,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using old.inner.buffer
  have sourceBytes : (MemoryRegion.mk address.toNat added.size).HasBytes s.external added := by
    rcases source with seed | empty
    · exact P256.Proofs.Program.hasBytes_copy seed.contents (seed_bytes ready.toFrameState seed)
    · subst added
      exact ⟨rfl, fun i => by have h : i.val < 0 := i.isLt; omega⟩
  have copied : (MemoryRegion.mk (scratch initial + 320 + BitVec.ofNat 64 (input.size % 64)).toNat added.size).HasBytes t.external added := by
    apply P256.Proofs.Program.hasBytes_copy sourceBytes
    intro i hi
    rw [show scratch initial + 320 + BitVec.ofNat 64 (input.size % 64) =
      stackPtr initial - BitVec.ofNat 64 (360-input.size%64) by simp only [scratch]; bv_omega]
    exact result.copied i hi
  have buffer := hasBytes_append (first := SHA256.remainderBytes input) (second := added)
    (by simpa only [SHA256.remainderBytes_size] using oldBuffer)
    (by simpa only [SHA256.remainderBytes_size] using copied)
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨fuel,t,run,ctx,result.rip,
    (result.calleeSaved .rbp (by decide +kernel)).trans ready.current,
    (result.calleeSaved .r13 (by decide +kernel)).trans ready.copyPointer,old,?_,
    (result.calleeSaved .r14 (by decide +kernel)).trans ready.position,
    (result.calleeSaved .rbx (by decide +kernel)).trans ready.length⟩
  simpa only [ByteArray.size_append,SHA256.remainderBytes_size] using buffer

end P256.Proofs.Nonce.Update.Seeded.Absorb
