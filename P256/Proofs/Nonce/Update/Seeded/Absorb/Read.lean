import P256.Proofs.Nonce.Update.Seeded.Absorb.Head
import P256.Proofs.Nonce.Update.Seeded.Absorb.Memory
import P256.Proofs.Nonce.Update.Absorb.SeedMemory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb

structure Read [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (index : Nat) (address : BitVec 64) (len : Nat) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a7ab
  current : s.regValue .rbp = initial.regValue .rsi + BitVec.ofNat 64 (16 * index)
  hashPointer : s.regValue .r14 = scratch initial + 384
  copyPointer : s.regValue .r13 = 0x11c930
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key input
  source : s.regValue .rsi = address
  length : s.regValue .rbx = BitVec.ofNat 64 len
  position : s.regValue .rdi = BitVec.ofNat 64 (input.size % 64)
  capacity : s.regValue .rdx = 64 - BitVec.ofNat 64 (input.size % 64)
  remaining : s.regValue .r15 = BitVec.ofNat 64 len - (64 - BitVec.ofNat 64 (input.size % 64))
  carry : (StatusFlags.ofRFLAGS s.RFLAGS).CF =
    (subSpec (BitVec.ofNat 64 len) (64 - BitVec.ofNat 64 (input.size % 64))).2.CF

theorem read [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced input : ByteArray} {index len : Nat} {address : BitVec 64}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (loop : Loop initial s state input index) (indexBound : index < 3)
    (pointer : loadBytes initial.external (initial.regValue .rsi + BitVec.ofNat 64 (16 * index)) 8 = .ok address)
    (length : loadBytes initial.external (initial.regValue .rsi + BitVec.ofNat 64 (16 * index + 8)) 8 = .ok (BitVec.ofNat 64 len)) :
    ∃ fuel t, Advances boundary fuel s t ∧ Read initial t state input index address len := by
  have hp : Head.Pre s := by
    refine ⟨loop.rip, ?_, ?_, ?_⟩
    · change MemReadable s (s.regValue .rbp) 8
      rw [loop.current]
      exact descriptor_readable pre loop.toFrameState (by omega)
    · change MemReadable s (s.regValue .rbp + 8) 8
      rw [loop.current]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        descriptor_readable (offset := 16 * index + 8) (len := 8) pre loop.toFrameState (by omega)
    · exact ScalarFrame.stack_readable pre.toDrbgCalleePre.callee loop.toFrameState (by decide) (by decide)
  have ptr : memLoad s.external (s.regValue .rbp) 64 = address := by
    rw [loop.current]
    exact descriptor_load pre loop.toFrameState (by omega) pointer
  have lengthS : Head.length s = BitVec.ofNat 64 len := by
    change memLoad s.external (s.regValue .rbp + 8) 64 = _
    rw [loop.current]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      descriptor_load pre loop.toFrameState (by omega) length
  have position : Head.position s = BitVec.ofNat 64 (input.size % 64) := by
    have pos := loop.hmac.inner.position
    have rem : (HMAC.keyPad state.key 0x36 ++ input).size % 64 = input.size % 64 := by
      rw [ByteArray.size_append,HMAC.keyPad_size]
      omega
    simp only [rem,BitVec.add_assoc,BitVec.reduceAdd] at pos
    change (memLoad s.external (stackPtr s + 383) 8).setWidth 64 = _
    rw [loop.rsp,memLoad_8]
    change ((s.external[scratch initial + 383]?).getD 0).toBitVec.setWidth 64 = _
    simp only [BitVec.ofNat_eq_ofNat] at pos ⊢
    rw [pos]
    simp only [Option.getD_some,UInt8.toBitVec_ofNat']
    bv_omega
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Head.run boundary pre.outerBoundary s
    (readyToStep loop.machine loop.bindingsSupported) (Head.code loop.loaded) hp
  have agrees : AgreesExcept [.reg 6,.reg 3,.reg 7,.reg 2,.reg 15,.flags,.rip] s t := effect.agrees
  have ctx := loop.toContext.after_nomem pre.toDrbgCalleePre ready agrees (by simp) (by simp)
    (by simp [Component.Covers])
  have h := effect.writes
  change t.regValue .rsi = memLoad s.external (s.regValue .rbp) 64 ∧
    t.regValue .rbx = Head.length s ∧ t.regValue .rdi = Head.position s ∧
    t.regValue .rdx = 64 - Head.position s ∧ t.regValue .r15 = Head.length s - (64 - Head.position s) at h
  rw [ptr,lengthS,position] at h
  refine ⟨fuel,t,run,ctx,effect.rip,
    (agrees.read (n := 64) (r := 5) (by simp)).trans loop.current,
    (agrees.read (n := 64) (r := 14) (by simp)).trans loop.hashPointer,
    (agrees.read (n := 64) (r := 13) (by simp)).trans loop.copyPointer,
    loop.hmac.copy (fun _ _ => by rw [agrees.external (by simp [Component.Covers])]),
    h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,?_⟩
  have flags := effect.flags.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).CF = (subSpec (Head.length s) (64 - Head.position s)).2.CF at flags
  rwa [lengthS,position] at flags

end P256.Proofs.Nonce.Update.Seeded.Absorb
