import P256.Proofs.Nonce.Update.Seeded.Prepare.PadSetup
import P256.Proofs.Nonce.Update.Seeded.Prepare.Memory
import P256.Proofs.HMAC.Pad

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem pad_memory [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {loop : HMAC.Pad.Loop}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state) (offset : loop.offset = 0) :
    HMAC.Pad.Memory loop s := by
  have buffer : HMAC.Pad.buffer loop s = stackPtr s + 0#64 := by
    simp only [HMAC.Pad.buffer, offset]
  constructor
  · rw [buffer]
    exact stack_writable current.toFrameState pre (by decide) (by decide) (by decide) (by decide)
  · intro i hi inside
    rw [buffer, stack_address current.toFrameState (by decide : 0 ≤ 680)] at inside
    exact pre.avoids (Stack.region initial 1856) (by simp) _
      (ScalarFrame.stack_contains pre.callee (offset := 680) (len := 64) (by decide) (by decide) ⟨i, hi, rfl⟩) (.inl inside)

theorem pad_copied [Bindings] {initial s t : RamState} {state : State} {loop : HMAC.Pad.Loop}
    (current : Context initial s state) (offset : loop.offset = 0)
    (post : HMAC.Pad.Post loop s t) {start len : Nat}
    (apart : OffsetsApart (BitVec.ofNat 64 start) len 0 64) (bound : len + 64 < 2^64) :
    ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 start + BitVec.ofNat 64 i]? =
      s.external[scratch initial + BitVec.ofNat 64 start + BitVec.ofNat 64 i]? := by
  intro i hi
  apply post.agrees.byte
  intro c member covered
  simp only [HMAC.Pad.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, equal⟩ := covered
  change scratch initial + BitVec.ofNat 64 start + BitVec.ofNat 64 i =
    stackPtr s + BitVec.ofNat 64 loop.offset + BitVec.ofNat 64 j at equal
  rw [offset, show stackPtr s = scratch initial from current.rsp] at equal
  exact OffsetsApart.ne (len₁ := len) (len₂ := 64)
    apart (scratch initial) hi hj bound equal

theorem Context.after_pad [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {original state : State} {loop : HMAC.Pad.Loop}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state) (offset : loop.offset = 0)
    (ready : ReadyToStep t) (post : HMAC.Pad.Post loop s t) :
    Context initial t state := by
  apply current.after_agrees pre ready post.agrees
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals simp [HMAC.Pad.footprint]
  · intro c member a covered
    simp only [HMAC.Pad.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    change (Component.mem (stackPtr s + BitVec.ofNat 64 loop.offset) 64).Covers a at covered
    rw [offset, show stackPtr s = scratch initial from current.rsp] at covered
    exact Update.Prepare.work_contains_scratch pre (by decide) covered
  · exact pad_copied current offset post (by unfold OffsetsApart; decide +kernel) (by decide)

theorem inner_pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Keyed initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ InnerPadded initial t state := by
  obtain ⟨n, u, setupRun, ready, _, effect⟩ := PadSetup.inner_run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported) (PadSetup.inner_code current.loaded) current.rip
  have agrees : AgreesExcept [.reg 0, .rip] s u := effect.agrees
  have context : Context initial u state := current.toContext.after_agrees pre ready agrees
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp)
    (by intro c hc a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl <;> exact ha.elim)
    (by intro i hi; rw [agrees.external (by simp [Component.Covers])])
  have key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes u.external
      (HMAC.keyPad state.key 0) := by
    rw [agrees.external (by simp [Component.Covers])]
    exact current.key
  have loopPre : HMAC.Pad.Pre .seededInner u :=
    ⟨pad_memory pre context rfl, effect.rip, effect.writes⟩
  obtain ⟨t, loopRun, readyT, _, post⟩ := HMAC.Pad.loop_correct ready context.loaded pre.outerBoundary loopPre
  refine ⟨n + 112, t, setupRun.trans loopRun, context.after_pad pre rfl readyT post, post.rip, ?_⟩
  have buffer : HMAC.Pad.buffer .seededInner u = scratch initial := by
    change stackPtr u + 0 = _
    simp only [context.rsp, scratch, show (0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]
  simpa only [buffer, BitVec.add_zero, HMAC.Pad.Loop.mask, show (0 : UInt8) ^^^ 0x36 = 0x36 from by decide] using
    post.keyPad state.key 0 (by simpa only [buffer, BitVec.add_zero] using key)

theorem outer_pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Compressed initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ OuterPadded initial t state := by
  have setupPre : PadSetup.OuterPre s := by
    refine ⟨current.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 319#64) 1
      rw [stack_address current.toFrameState (by decide : 319 ≤ 680)]
      exact writable_of_grow
        (stack_sub_writable pre.stack
          (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
          (by decide) (by decide) (by decide) (by omega)) current.allocated
    · exact stack_codeApart current.toFrameState pre (offset := 319) (len := 1) (pc := 0xa561) (codeLen := 15) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n, u, setupRun, ready, _, effect⟩ := PadSetup.outer_run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported) (PadSetup.outer_code current.loaded) setupPre
  have agrees : AgreesExcept [.mem (rspOf s + 319) 1, .reg 0, .rip] s u := by
    simpa only [PadSetup.outerEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.append_assoc, List.nil_append, List.cons_append,
      Nat.reduceDiv] using effect.agrees
  have rsp : rspOf s = scratch initial := current.rsp
  have context : Context initial u state := by
    apply current.toContext.after_agrees pre ready agrees
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    · intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rw [rsp] at ha
        exact Update.Prepare.work_contains_scratch pre (by decide) ha
      all_goals exact ha.elim
    · intro i hi
      apply agrees.byte
      intro c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · obtain ⟨j, hj, equal⟩ := ha
        rw [rsp] at equal
        exact OffsetsApart.ne (len₁ := 24) (len₂ := 1)
          (by unfold OffsetsApart; decide +kernel : OffsetsApart 64 24 319 1)
          (scratch initial) hi hj (by decide) equal
      all_goals exact ha.elim
  have readable : MemReadable u (rspOf s + 319) 1 := by
    rw [rsp, ← show stackPtr u = scratch initial from context.rsp]
    exact stack_readable context.toFrameState pre (by decide) (by decide) (by decide)
  have newPosition : u.external[rspOf s + 319]? = some 0 := by
    have written := effect.writes.1
    change memLoad u.external (rspOf s + 319) 8 = 0 at written
    have bytes := Bytes.of_memLoad (n := 8) readable.mem
    rw [written] at bytes
    simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using
      bytes 0 (by decide)
  have oldPosition : s.external[rspOf s + 319]? = some 0 := by
    simpa only [rsp, HMAC.keyPad_size, Nat.reduceMod, UInt8.reduceOfNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using current.inner.position
  have copied : ∀ a : BitVec 64, u.external[a]? = s.external[a]? := by
    intro a
    by_cases equal : a = rspOf s + 319
    · subst a
      exact newPosition.trans oldPosition.symm
    · apply agrees.byte
      intro c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · obtain ⟨i, hi, eq⟩ := ha
        have iz : i = 0 := by omega
        simp only [iz, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at eq
        exact equal eq
      all_goals exact ha.elim
  have key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes u.external
      (HMAC.keyPad state.key 0x36) := hasBytes_copy current.key (fun i hi => copied _)
  have inner : HMAC.Sha256StateAt u (scratch initial + 256) (HMAC.keyPad state.key 0x36) :=
    current.inner.copy (fun i hi => copied _)
  have loopPre : HMAC.Pad.Pre .seededOuter u :=
    ⟨pad_memory pre context rfl, effect.rip, effect.writes.2⟩
  obtain ⟨t, loopRun, readyT, _, post⟩ := HMAC.Pad.loop_correct ready context.loaded pre.outerBoundary loopPre
  refine ⟨n + 112, t, setupRun.trans loopRun, context.after_pad pre rfl readyT post, post.rip, ?_, ?_, ?_⟩
  · exact (post.agrees.read (n := 64) (r := 12) (by simp [HMAC.Pad.footprint])).trans
      ((agrees.read (n := 64) (r := 12) (by simp)).trans current.bufferPointer)
  · have buffer : HMAC.Pad.buffer .seededOuter u = scratch initial := by
      change stackPtr u + 0 = _
      simp only [context.rsp, scratch, show (0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]
    simpa only [buffer, BitVec.add_zero, HMAC.Pad.Loop.mask, show (0x36 : UInt8) ^^^ 0x6a = 0x5c from by decide] using
      post.keyPad state.key 0x36 (by simpa only [buffer, BitVec.add_zero] using key)
  · exact inner.copy (pad_copied context rfl post (by unfold OffsetsApart; decide +kernel) (by decide))

end P256.Proofs.Nonce.Update.Seeded.Prepare
