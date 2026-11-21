import P256.Proofs.Nonce.Update.Absorb.Seeded.CrossCopy
import P256.Proofs.Nonce.Update.Absorb.Seeded.CompressionSetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Compressed [Bindings] (initial s : RamState) (state : State) (input secret : ByteArray)
    (address : BitVec 64) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a320
  current : s.regValue .r14 = initial.regValue .rsi
  outer : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external (HMAC.keyPad state.key 0x5c)
  hash : SHA256.HashStateAt s (scratch initial + 216)
    (P256.Proofs.SHA256.Reference.compress
      (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input))
      (Standards.NIST.SHA2.bytesToBits (input ++ secret.extract 0 31)))
  count : loadBytes s.external (scratch initial + 248) 8 = .ok (2 : BitVec 64)
  tail : s.regValue .r15 = address + 31
  remaining : s.regValue .rbx = 1

def compressionLayout : StackCallLayout 1856 64 32 336 :=
  ⟨688,528,464,by decide,by decide,by decide,by decide,by decide,by decide,.inl (by decide)⟩

set_option maxHeartbeats 1000000 in
theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (copied : CrossCopied initial s state input secret address) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compressed initial t state input secret address := by
  have hp : CompressionSetup.Pre s := ⟨copied.rip,
    stack_writable8 pre copied.toFrameState (by decide) (by decide),
    fun pc len bound => ScalarFrame.stack_code pre.callee copied.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨fuel,u,run,ready,_,effect⟩ := CompressionSetup.run boundary pre.outerBoundary s
    (readyToStep copied.machine copied.bindingsSupported) (CompressionSetup.code copied.loaded) hp
  have agrees : AgreesExcept [.mem (scratch initial + 248) 8,.reg 2,.reg 7,.reg 6,.flags,.rip] s u := by
    have h := effect.agrees
    simp only [CompressionSetup.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf s = scratch initial from copied.rsp] at h
  have writes : InnerWrites initial [.mem (scratch initial + 248) 8,.reg 2,.reg 7,.reg 6,.flags,.rip] := by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i,hi,rfl⟩ := cover
    refine ⟨96+i,by omega,?_⟩; bv_omega
  have ctx := copied.toContext.after_inner pre ready agrees (by simp) (by simp) writes
  have kept (offset len : Nat) (bound : offset+len < 2^64) (apart : offset+len ≤ 248 ∨ 256 ≤ offset) :
      ∀ i < len, u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j,hj,eq⟩ := cover; bv_omega
  have oldCount : memLoad s.external (scratch initial + 248) 64 = 1 := by
    have readable := ScalarFrame.stack_readable pre.callee copied.toFrameState (offset:=248) (len:=8) (by decide) (by decide)
    rw [show stackPtr s = scratch initial from copied.rsp] at readable
    exact Except.ok.inj ((Bytes.of_memLoad (n:=64) readable.mem).loadBytes64.symm.trans copied.count)
  have stores := effect.writes
  change memLoad u.external (stackPtr s + 248) 64 = memLoad s.external (stackPtr s + 248) 64 + 1 ∧
    u.regValue .rdx = 1 ∧ u.regValue .rdi = stackPtr s + 216 ∧ u.regValue .rsi = s.regValue .r13 at stores
  rw [show stackPtr s = scratch initial from copied.rsp,oldCount,copied.buffer] at stores
  have countU : loadBytes u.external (scratch initial + 248) 8 = .ok (2 : BitVec 64) := by
    have readable := ScalarFrame.stack_readable pre.callee ctx.toFrameState (offset:=248) (len:=8) (by decide) (by decide)
    rw [show stackPtr u = scratch initial from ctx.rsp] at readable
    have bytes := (Bytes.of_memLoad (n:=64) readable.mem).loadBytes64
    have h := stores.1
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [h] at bytes
    exact bytes
  have addr320 : scratch initial + 152#64 = stackPtr initial - 528#64 := by simp only [scratch]; bv_omega
  have addr384 : scratch initial + 216#64 = stackPtr initial - 464#64 := by simp only [scratch]; bv_omega
  have block : (MemoryRegion.mk (stackPtr initial - 528#64).toNat 64).HasBytes u.external (input ++ secret.extract 0 31) := by
    rw [← addr320]
    exact P256.Proofs.Program.hasBytes_copy copied.block (kept 152 64 (by decide) (by decide))
  have hash : SHA256.HashStateAt u (stackPtr initial - 464#64)
      (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input)) := by
    rw [← addr384]
    exact SHA256.HashStateAt.copy copied.hash (kept 216 32 (by decide) (by decide))
  obtain ⟨t,result⟩ := compression_call (depth := 680) pre ctx.toFrameState compressionLayout
    rfl (by decide) (by decide) 0xa31b 0xb670 (by decide)
    (by decide +kernel) (by decide) effect.rip
    (by simpa only [compressionLayout,BitVec.ofNat_eq_ofNat,addr320] using stores.2.2.2)
    (by simpa only [compressionLayout,BitVec.ofNat_eq_ofNat,addr384] using stores.2.2.1)
    stores.2.1 block hash
  have finalBytes (offset len : Nat) (bound : offset ≤ 680) (span : offset+len ≤ 688)
      (apart : offset+len ≤ 216 ∨ 248 ≤ offset) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [show scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680-offset) by simp only [scratch]; bv_omega]
    exact result.stack_byte (offset := 680 - offset) (len := len) pre (by decide) (by decide) (by omega) (by omega) (by simp only [compressionLayout]; omega) hi
  have ctxT : Context initial t state := by
    apply ctx.after result.toFrameState result.drbg (result.calleeSaved .rbp (by decide +kernel))
    intro off member i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact finalBytes 64 8 (by decide) (by decide) (by decide) i hi
    · exact finalBytes 72 8 (by decide) (by decide) (by decide) i hi
    · exact finalBytes 80 8 (by decide) (by decide) (by decide) i hi
    · exact finalBytes 424 8 (by decide) (by decide) (by decide) i hi
  obtain ⟨compressionFuel,compressionRun⟩ := result.execution
  refine ⟨fuel+compressionFuel,t,run.trans compressionRun,ctxT,result.rip,
    (result.calleeSaved .r14 (by decide +kernel)).trans ((agrees.read (n:=64) (r:=14) (by simp)).trans copied.current),?_,?_,
    P256.Proofs.Program.loadBytes_ok_copy (finalBytes 248 8 (by decide) (by decide) (by decide)) countU,
    (result.calleeSaved .r15 (by decide +kernel)).trans ((agrees.read (n:=64) (r:=15) (by simp)).trans copied.tail),
    (result.calleeSaved .rbx (by decide +kernel)).trans ((agrees.read (n:=64) (r:=3) (by simp)).trans copied.remaining)⟩
  · exact P256.Proofs.Program.hasBytes_copy (P256.Proofs.Program.hasBytes_copy copied.outer (kept 88 64 (by decide) (by decide)))
      (finalBytes 88 64 (by decide) (by decide) (by decide))
  · have h := result.hash
    rw [SHA256.compressBlocks_single _ _ copied.block.1] at h
    simpa only [compressionLayout,BitVec.ofNat_eq_ofNat,addr384] using h

end P256.Proofs.Nonce.Update.Absorb.Seeded
