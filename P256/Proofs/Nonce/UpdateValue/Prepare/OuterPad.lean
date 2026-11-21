import P256.Proofs.Nonce.UpdateValue.Prepare.Pad
import P256.Proofs.Nonce.UpdateValue.Prepare.PadSetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem outer_pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (input : Compressed initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ OuterPadded initial t state := by
  have setupPre : PadSetup.OuterPre s := by
    refine ⟨input.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 167) 1
      rw [show stackPtr s + 167 = stackPtr initial - 321 from
        ScalarFrame.scalar_stack_address input.rsp (by decide) (by decide : 167 ≤ 488)]
      exact writable_of_grow
        (stack_sub_writable pre.stack
          (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
          (by decide) (by decide) (by decide) (by omega)) input.allocated
    · exact ScalarFrame.stack_code pre.callee input.toFrameState (by decide)
        (offset := 167) (len := 1) (codeOffset := 0xaa24) (codeLen := 28)
        (by decide) (by decide)
  obtain ⟨fuel, u, run, ready, _, effect⟩ := PadSetup.outer_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (PadSetup.outer_code input.loaded) setupPre
  have rsp : rspOf s = scratch initial := input.rsp
  have agrees : AgreesExcept [.mem (scratch initial + 167) 1, .reg 0, .rip] s u := by
    simpa only [PadSetup.outerEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      List.append_nil, Nat.reduceDiv, rsp] using effect.agrees
  have stored : memLoad u.external (scratch initial + 167) 8 = 0 := by
    have h : memLoad u.external (rspOf s + 167) 8 = 0 := effect.writes.1
    rwa [rsp] at h
  have positionU : u.external[scratch initial + 167]? = some 0 := by
    have readable := readable_of_grow
      (ScalarFrame.stack_readable pre.callee input.toFrameState (by decide) (offset := 167)
        (len := 1) (by decide)) agrees.grow
    have sp : stackPtr s = scratch initial := input.rsp
    rw [sp] at readable
    have bytes := Bytes.of_memLoad (n := 8) (a := scratch initial + 167) readable.mem
    rw [stored] at bytes
    simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using
      bytes 0 (by decide)
  have positionS : s.external[scratch initial + 167]? = some 0 := by
    simpa only [HMAC.keyPad_size, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat, UInt8.reduceOfNat] using input.inner.position
  have memory : u.external = s.external := by
    apply Std.ExtHashMap.ext_getElem?
    intro a
    by_cases same : a = scratch initial + 167
    · subst a
      exact positionU.trans positionS.symm
    · apply agrees.memory
      intro c member covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · obtain ⟨i, hi, address⟩ := covered
        have zero : i = 0 := by omega
        subst i
        simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at address
        exact same address
      · exact covered.elim
      · exact covered.elim
  have context := input.toContext.after_agrees pre ready agrees
    (by intro r member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp)
    (by intro c member a covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact work_contains_scratch pre (by decide) covered
        all_goals exact covered.elim)
  have key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes u.external
      (HMAC.keyPad state.key 0x36) := by rw [memory]; exact input.key
  have inner : HMAC.Sha256StateAt u (scratch initial + 104) (HMAC.keyPad state.key 0x36) :=
    input.inner.copy (fun _ _ => by rw [memory])
  obtain ⟨t, loopRun, contextT, post, bytesT⟩ := pad_run (loop := .valueOuter) pre context
    rfl effect.rip effect.writes.2 0x36 key
  have full := agrees.trans post.agrees
  refine ⟨fuel + 112, t, run.trans loopRun, contextT, post.rip,
    (full.read (n := 64) (r := 14) (by simp [HMAC.Pad.footprint])).trans input.bufferPointer,
    bytesT, ?_⟩
  apply inner.copy
  intro i hi
  apply post.agrees.byte
  intro c member covered
  simp only [HMAC.Pad.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  have buffer : HMAC.Pad.buffer .valueOuter u = scratch initial + 8 := by
    simp only [HMAC.Pad.buffer, HMAC.Pad.Loop.offset, context.rsp, scratch, BitVec.ofNat_eq_ofNat]
  rw [buffer] at covered
  obtain ⟨j, hj, eq⟩ := covered
  exact OffsetsApart.ne (len₂ := 104) (by unfold OffsetsApart; decide +kernel)
    (scratch initial) hj hi (by decide) eq.symm

end P256.Proofs.Nonce.UpdateValue.Prepare
