import P256.Proofs.Nonce.Update.Seeded.Absorb.CrossCopy
import P256.Proofs.Nonce.Update.Seeded.Absorb.CompressionSetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Compressed [Bindings] (initial s : RamState) (state : State) (input secret : ByteArray)
    (address : BitVec 64) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a7d8
  current : s.regValue .rbp = initial.regValue .rsi
  hashPointer : s.regValue .r14 = scratch initial + 384
  copyPointer : s.regValue .r13 = 0x11c930
  outer : (MemoryRegion.mk (scratch initial + 256).toNat 64).HasBytes s.external (HMAC.keyPad state.key 0x5c)
  hash : SHA256.HashStateAt s (scratch initial + 384)
    (P256.Proofs.SHA256.Reference.compress
      (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input))
      (Standards.NIST.SHA2.bytesToBits (input ++ secret.extract 0 31)))
  count : loadBytes s.external (scratch initial + 416) 8 = .ok (2 : BitVec 64)
  tail : s.regValue .rbx = address + 31
  remaining : s.regValue .r15 = 1

def compressionLayout : StackCallLayout 1856 64 32 336 :=
  ⟨688,360,296,by decide,by decide,by decide,by decide,by decide,by decide,.inl (by decide)⟩

set_option maxHeartbeats 1000000 in
theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (copied : CrossCopied initial s state input secret address) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compressed initial t state input secret address := by
  have hp : CompressionSetup.Pre s := ⟨copied.rip,
    Update.Absorb.stack_writable8 pre copied.toFrameState (by decide) (by decide),
    fun pc len bound => ScalarFrame.stack_code pre.callee copied.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨fuel,u,run,ready,_,effect⟩ := CompressionSetup.run boundary pre.outerBoundary s
    (readyToStep copied.machine copied.bindingsSupported) (CompressionSetup.code copied.loaded) hp
  have agrees : AgreesExcept [.mem (scratch initial + 416) 8,.reg 2,.reg 7,.reg 6,.flags,.rip] s u := by
    have h := effect.agrees
    simp only [CompressionSetup.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf s = scratch initial from copied.rsp] at h
  have writes : InnerWrites initial [.mem (scratch initial + 416) 8,.reg 2,.reg 7,.reg 6,.flags,.rip] := by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i,hi,rfl⟩ := cover
    refine ⟨96+i,by omega,?_⟩; bv_omega
  have ctx := copied.toContext.after_inner pre ready agrees (by simp) (by simp) writes
  have kept (offset len : Nat) (bound : offset+len < 2^64) (apart : offset+len ≤ 416 ∨ 424 ≤ offset) :
      ∀ i < len, u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j,hj,eq⟩ := cover; bv_omega
  have oldCount : memLoad s.external (scratch initial + 416) 64 = 1 := by
    have readable := ScalarFrame.stack_readable pre.callee copied.toFrameState (offset:=416) (len:=8) (by decide) (by decide)
    rw [show stackPtr s = scratch initial from copied.rsp] at readable
    exact Except.ok.inj ((Bytes.of_memLoad (n:=64) readable.mem).loadBytes64.symm.trans copied.count)
  have stores := effect.writes
  change memLoad u.external (stackPtr s + 416) 64 = memLoad s.external (stackPtr s + 416) 64 + 1 ∧
    u.regValue .rdx = 1 ∧ u.regValue .rdi = s.regValue .r14 ∧ u.regValue .rsi = s.regValue .r12 at stores
  rw [show stackPtr s = scratch initial from copied.rsp,oldCount,copied.hashPointer,copied.bufferPointer] at stores
  have countU : loadBytes u.external (scratch initial + 416) 8 = .ok (2 : BitVec 64) := by
    have readable := ScalarFrame.stack_readable pre.callee ctx.toFrameState (offset:=416) (len:=8) (by decide) (by decide)
    rw [show stackPtr u = scratch initial from ctx.rsp] at readable
    have bytes := (Bytes.of_memLoad (n:=64) readable.mem).loadBytes64
    have h := stores.1
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [h] at bytes
    exact bytes
  have addr152 : scratch initial + 320#64 = stackPtr initial - 360#64 := by simp only [scratch]; bv_omega
  have addr216 : scratch initial + 384#64 = stackPtr initial - 296#64 := by simp only [scratch]; bv_omega
  have block : (MemoryRegion.mk (stackPtr initial - 360#64).toNat 64).HasBytes u.external (input ++ secret.extract 0 31) := by
    rw [← addr152]
    exact P256.Proofs.Program.hasBytes_copy copied.block (kept 320 64 (by decide) (by decide))
  have hash : SHA256.HashStateAt u (stackPtr initial - 296#64)
      (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input)) := by
    rw [← addr216]
    exact SHA256.HashStateAt.copy copied.hash (kept 384 32 (by decide) (by decide))
  obtain ⟨t,result⟩ := compression_call (depth := 680) pre ctx.toFrameState compressionLayout
    rfl (by decide) (by decide) 0xa7d3 0xb1b8 (by decide)
    (by decide +kernel) (by decide) effect.rip
    (by simpa only [compressionLayout,BitVec.ofNat_eq_ofNat,addr152] using stores.2.2.2)
    (by simpa only [compressionLayout,BitVec.ofNat_eq_ofNat,addr216] using stores.2.2.1)
    stores.2.1 block hash
  have finalBytes (offset len : Nat) (bound : offset ≤ 680) (span : offset+len ≤ 688)
      (apart : offset+len ≤ 384 ∨ 416 ≤ offset) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [show scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680-offset) by simp only [scratch]; bv_omega]
    exact result.stack_byte (offset := 680-offset) (len := len) pre (by decide) (by decide) (by omega) (by omega) (by simp only [compressionLayout]; omega) hi
  have ctxT : Context initial t state := by
    exact ctx.after result.toFrameState (ctx.drbg.copy result.drbg)
      ((result.calleeSaved .r12 (by simp)).trans ctx.bufferPointer)
      (by simpa only [BitVec.ofNat_eq_ofNat] using finalBytes 64 24 (by decide) (by decide) (by decide))
  obtain ⟨compressionFuel,compressionRun⟩ := result.execution
  refine ⟨fuel+compressionFuel,t,run.trans compressionRun,ctxT,result.rip,
    (result.calleeSaved .rbp (by decide +kernel)).trans ((agrees.read (n:=64) (r:=5) (by simp)).trans copied.current),
    (result.calleeSaved .r14 (by decide +kernel)).trans ((agrees.read (n:=64) (r:=14) (by simp)).trans copied.hashPointer),
    (result.calleeSaved .r13 (by decide +kernel)).trans ((agrees.read (n:=64) (r:=13) (by simp)).trans copied.copyPointer),?_,?_,
    P256.Proofs.Program.loadBytes_ok_copy (finalBytes 416 8 (by decide) (by decide) (by decide)) countU,
    (result.calleeSaved .rbx (by decide +kernel)).trans ((agrees.read (n:=64) (r:=3) (by simp)).trans copied.tail),
    (result.calleeSaved .r15 (by decide +kernel)).trans ((agrees.read (n:=64) (r:=15) (by simp)).trans copied.remaining)⟩
  · exact P256.Proofs.Program.hasBytes_copy (P256.Proofs.Program.hasBytes_copy copied.outer (kept 256 64 (by decide) (by decide)))
      (finalBytes 256 64 (by decide) (by decide) (by decide))
  · have h := result.hash
    rw [SHA256.compressBlocks_single _ _ copied.block.1] at h
    simpa only [compressionLayout,BitVec.ofNat_eq_ofNat,addr216] using h

end P256.Proofs.Nonce.Update.Seeded.Absorb
