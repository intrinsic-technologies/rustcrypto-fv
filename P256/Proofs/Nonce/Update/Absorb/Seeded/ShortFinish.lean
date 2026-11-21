import P256.Proofs.Nonce.Update.Absorb.Seeded.ShortCopy
import P256.Proofs.Nonce.Update.Absorb.Seeded.ShortTail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Finished [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (index : Nat) : Prop extends Context initial s state where
  rip : s.RIP = if index = 2 then 0x10a39c else 0x10a2c3
  current : s.regValue .r14 = initial.regValue .rsi + BitVec.ofNat 64 (16 * (index + 1))
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key input

theorem finish_short [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced input added : ByteArray} {index : Nat}
    (pre : UpdateSeededPre initial boundary state secret reduced)
    (copied : ShortCopied initial s state input added index)
    (short : input.size % 64 + added.size < 64) (indexBound : index < 3) :
    ∃ fuel t, Advances boundary fuel s t ∧ Finished initial t state (input ++ added) index := by
  have hp : ShortTail.Pre s := ⟨copied.rip,
    ScalarFrame.stack_readable pre.callee copied.toFrameState (by decide) (by decide),
    stack_writable1 pre.toDrbgCalleePre copied.toFrameState (by decide),fun pc len bound =>
      ScalarFrame.stack_code pre.callee copied.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨fuel,u,run,ready,_,effect⟩ := ShortTail.run boundary pre.outerBoundary s
    (readyToStep copied.machine copied.bindingsSupported) (ShortTail.code copied.loaded) hp
  have agrees : AgreesExcept [.reg 15,.mem (scratch initial + 215) 1,.reg 14,.flags,.rip] s u := by
    have h := effect.agrees
    simp only [ShortTail.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf s = scratch initial from copied.rsp] at h
  have writes : InnerWrites initial [.reg 15,.mem (scratch initial + 215) 1,.reg 14,.flags,.rip] := by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i,hi,rfl⟩ := cover
    refine ⟨63+i,by omega,?_⟩
    bv_omega
  have ctx := copied.toContext.after_inner pre.toDrbgCalleePre ready agrees (by simp) (by simp) writes
  have bytes (offset len : Nat) (bound : offset+len < 2^64) (apart : offset+len ≤ 215 ∨ 216 ≤ offset) :
      ∀ i < len, u.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j,hj,eq⟩ := cover
    bv_omega
  have sum : ShortTail.sum s = BitVec.ofNat 8 (input.size % 64 + added.size) := by
    change (s.regValue .r15).setWidth 8 + (s.regValue .rbx).setWidth 8 = _
    rw [copied.length,copied.position]
    bv_omega
  have stores := effect.writes
  change u.regValue .r15 = _ ∧ memLoad u.external (stackPtr s + 215) 8 = ShortTail.sum s ∧
    u.regValue .r14 = s.regValue .r14 + 16 at stores
  have pos : u.external[scratch initial + 215]? = some (UInt8.ofNat (input.size % 64 + added.size)) := by
    apply scratch_byte_of_load pre.toDrbgCalleePre ctx.toFrameState 215 (by decide)
      (BitVec.ofNat 8 (input.size % 64 + added.size))
    simpa only [copied.rsp,sum,scratch,BitVec.ofNat_eq_ofNat] using stores.2.1
  have hmac : HMAC.HmacStateAt u (scratch initial + 88) state.key (input ++ added) := by
    apply hmacStateAt_append_small copied.hmac short
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using
        P256.Proofs.Program.hasBytes_copy copied.buffer (bytes 152 (input.size % 64 + added.size) (by omega) (by omega))
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using pos
    · intro i hi kept
      have h := bytes (88+i) 1 (by omega) (by rcases kept with left | right <;> omega) 0 (by decide)
      simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.add_zero] using h
  have current : u.regValue .r14 = initial.regValue .rsi + BitVec.ofNat 64 (16*(index+1)) := by
    rw [stores.2.2,copied.current]
    bv_omega
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = decide (index=2) := by
    have h := effect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((s.regValue .r14 + 16) - memLoad s.external (stackPtr s + 80) 64) == 0) at h
    rw [copied.current,show stackPtr s = scratch initial from copied.rsp,copied.savedEnd,pre.inputCount] at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq]
    bv_omega
  obtain ⟨t,step,readyT,branch⟩ := jcc_rel32_effect_step 0x10a2bd 4 0xd9 u ready
    (programText_slice (programLoaded_codeIn ctx.loaded) 0xa2bd _ (by decide) (by decide +kernel))
    ⟨effect.rip,by intro; decide⟩
  have rip : t.RIP = if index=2 then 0x10a39c else 0x10a2c3 := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10a39c else 0x10a2c3) = _
    simp only [zero,decide_eq_true_eq]
  have lastRun : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [rip]
    split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa39c (by decide))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa2c3 (by decide))))
  have a : AgreesExcept [.rip] u t := branch.agrees
  have ctxT := ctx.after_nomem pre.toDrbgCalleePre readyT a (by simp) (by simp) (by simp [Component.Covers])
  exact ⟨fuel+1,t,run.trans lastRun,ctxT,rip,
    (a.read (n:=64) (r:=14) (by simp)).trans current,
    hmac.copy (fun _ _ => by rw [a.external (by simp [Component.Covers])])⟩

end P256.Proofs.Nonce.Update.Absorb.Seeded
