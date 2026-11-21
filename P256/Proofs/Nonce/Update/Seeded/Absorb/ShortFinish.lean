import P256.Proofs.Nonce.Update.Seeded.Absorb.ShortCopy
import P256.Proofs.Nonce.Update.Seeded.Absorb.ShortTail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb
open Update.Absorb.Seeded (scratch_byte_of_load)

structure Finished [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (index : Nat) : Prop extends Context initial s state where
  rip : s.RIP = if index = 2 then 0x10a849 else 0x10a78d
  current : s.regValue .rbp = initial.regValue .rsi + BitVec.ofNat 64 (16 * (index + 1))
  hashPointer : s.regValue .r14 = scratch initial + 384
  copyPointer : s.regValue .r13 = 0x11c930
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key input

theorem finish_short [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced input added : ByteArray} {index : Nat}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (copied : ShortCopied initial s state input added index)
    (short : input.size % 64 + added.size < 64) (indexBound : index < 3) :
    ∃ fuel t, Advances boundary fuel s t ∧ Finished initial t state (input ++ added) index := by
  have hp : ShortTail.Pre s := ⟨copied.rip,
    ScalarFrame.stack_readable pre.toDrbgCalleePre.callee copied.toFrameState (by decide) (by decide),
    stack_writable1 pre.toDrbgCalleePre copied.toFrameState (by decide),fun pc len bound =>
      ScalarFrame.stack_code pre.toDrbgCalleePre.callee copied.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨fuel,u,run,ready,_,effect⟩ := ShortTail.run boundary pre.outerBoundary s
    (readyToStep copied.machine copied.bindingsSupported) (ShortTail.code copied.loaded) hp
  have agrees : AgreesExcept [.reg 3,.reg 14,.mem (scratch initial + 383) 1,.reg 5,.flags,.rip] s u := by
    have h := effect.agrees
    simp only [ShortTail.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf s = scratch initial from copied.rsp] at h
  have writes : InnerWrites initial [.reg 3,.reg 14,.mem (scratch initial + 383) 1,.reg 5,.flags,.rip] := by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i,hi,rfl⟩ := cover
    refine ⟨63+i,by omega,?_⟩
    bv_omega
  have ctx := copied.toContext.after_inner pre.toDrbgCalleePre ready agrees (by simp) (by simp) writes
  have bytes (offset len : Nat) (bound : offset+len < 2^64) (apart : offset+len ≤ 383 ∨ 384 ≤ offset) :
      ∀ i < len, u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j,hj,eq⟩ := cover
    bv_omega
  have sum : ShortTail.sum s = BitVec.ofNat 8 (input.size % 64 + added.size) := by
    change (s.regValue .rbx).setWidth 8 + (s.regValue .r14).setWidth 8 = _
    rw [copied.length,copied.position]
    bv_omega
  have stores := effect.writes
  change u.regValue .rbx = _ ∧ u.regValue .r14 = stackPtr s + 384 ∧
    memLoad u.external (stackPtr s + 383) 8 = ShortTail.sum s ∧
    u.regValue .rbp = s.regValue .rbp + 16 at stores
  have pos : u.external[scratch initial + 383]? = some (UInt8.ofNat (input.size % 64 + added.size)) := by
    apply scratch_byte_of_load pre.toDrbgCalleePre ctx.toFrameState 383 (by decide)
      (BitVec.ofNat 8 (input.size % 64 + added.size))
    simpa only [copied.rsp,sum,scratch,BitVec.ofNat_eq_ofNat] using stores.2.2.1
  have hmac : HMAC.HmacStateAt u (scratch initial + 256) state.key (input ++ added) := by
    apply hmacStateAt_append_small copied.hmac short
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using
        P256.Proofs.Program.hasBytes_copy copied.buffer (bytes 320 (input.size % 64 + added.size) (by omega) (by omega))
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using pos
    · intro i hi kept
      have h := bytes (256+i) 1 (by omega) (by rcases kept with left | right <;> omega) 0 (by decide)
      simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.add_zero] using h
  have current : u.regValue .rbp = initial.regValue .rsi + BitVec.ofNat 64 (16*(index+1)) := by
    rw [stores.2.2.2,copied.current]
    bv_omega
  have atEnd : ShortTail.atEnd s = decide (index=2) := by
    change ((s.regValue .rbp + 16) == memLoad s.external (stackPtr s + 80) 64) = _
    rw [copied.current,show stackPtr s = scratch initial from copied.rsp,copied.savedEnd,pre.inputCount]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq]
    bv_omega
  have rip : u.RIP = if index=2 then 0x10a849 else 0x10a78d := by
    rw [effect.rip]
    simp only [ShortTail.effect,ShortTail.target,atEnd,decide_eq_true_eq]
  refine ⟨fuel,u,run,ctx,rip,current,?_,
    (agrees.read (n:=64) (r:=13) (by simp)).trans copied.copyPointer,hmac⟩
  exact stores.2.1.trans (by rw [copied.rsp]; rfl)

end P256.Proofs.Nonce.Update.Seeded.Absorb
