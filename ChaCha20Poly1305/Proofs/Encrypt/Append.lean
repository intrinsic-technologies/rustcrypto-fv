import ChaCha20Poly1305.Proofs.Encrypt.Append.Update

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

theorem append_call [bindings : Bindings] {s : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} (boundary : ReturnBoundary)
    (pre : AppendPre s buffer length tag)
    (outside : ¬ InProgram boundary.rip)
    (different : boundary.rip ≠ (returnBoundary s).rip)
    (returnLow : (returnBoundary s).rip.toNat < 2 ^ 32) :
    ∃ fuel t, Advances boundary fuel s t ∧ AppendPost s t buffer length tag := by
  obtain ⟨u, au, atCopy⟩ := append_to_copy pre outside
  obtain ⟨fuel, c, t, adv, result, ct, hp, spc, retc, push⟩ := append_memcpy pre outside atCopy
  have agt := (atCopy.agrees.trans push).trans result.agrees
  have rt : t.RIP = 0x101fe2 := by rw [result.rip, retc]
  have spt : stackPtr t = stackPtr s - BitVec.ofNat 64 40 := by
    rw [result.rsp, spc]
    bv_omega
  have bt : rd t 3 = 16 := ((result.agrees.read (by simp [MemoryRoutines.callChanges])).trans
    (push.read (by simp))).trans atCopy.rbx
  have dt : rd t 14 = s.regValue .rdi := ((result.agrees.read (by simp
      [MemoryRoutines.callChanges])).trans
    (push.read (by simp))).trans atCopy.r14
  have lt : rd t 15 = BitVec.ofNat 64 length := ((result.agrees.read (by simp
      [MemoryRoutines.callChanges])).trans
    (push.read (by simp))).trans atCopy.r15
  obtain ⟨v, av, rv, cv, ipv, updateAg, word⟩ := append_update pre outside agt.grow
    result.ready ct rt dt lt bt
  have spv : stackPtr v = stackPtr s - BitVec.ofNat 64 40 :=
    sp_keep updateAg (by simp [appendUpdateChanges]) spt
  have descStack : (appendDescriptor s).Disjoint (Stack.region s 48) :=
    (List.pairwise_cons.mp pre.separation.1).1 _ (by simp)
  have descDst : (appendDescriptor s).Disjoint (appendDestination buffer length) :=
    (List.pairwise_cons.mp pre.separation.1).1 _ (by simp)
  have slots : ∀ k ≤ 40, wd v (stackPtr s - BitVec.ofNat 64 k) =
      wd u (stackPtr s - BitVec.ofNat 64 k) := by
    intro k hk
    refine (wd_congr ?_).trans (append_memcpy_keeps_stack_word pre atCopy push result hk)
    intro i hi
    exact append_update_keeps pre updateAg descStack
      (stack_slot_contains pre.stack (by omega) (by omega))
  obtain ⟨hroom, htop⟩ := stack_bounds pre.stack
  have returnU : wd u (stackPtr s) = (returnBoundary s).rip := by
    change wd u (stackPtr s) = wd s (stackPtr s)
    apply gload atCopy.agrees
    intro comp hc i hi
    simp only [appendPushChanges, appendBodyChanges, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact nonmem_not_covers rfl _
    all_goals
      apply mem_not_covers <;>
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have returnV : wd v (stackPtr s) = (returnBoundary s).rip := by
    have h := slots 0 (by omega)
    simp only [BitVec.sub_zero] at h
    exact h.trans returnU
  obtain ⟨fin, af, Tf, ipf, spf, zero, bfin, r12fin, r14fin, r15fin⟩ :=
    append_tail pre.stack (agt.trans updateAg).grow rv cv ipv spv outside
      (Ne.symm different) returnLow returnV
  have allAg := (agt.trans updateAg).trans Tf.agrees
  refine ⟨_, fin, au.trans (adv.trans (av.trans af)), ?_⟩
  refine ⟨⟨Tf.ready.smrr, Tf.ready.memoryType, pre.environment.stringStride,
      Tf.ready.features.lzcnt⟩,
    ⟨Tf.ready.cpu, SupportedSSE.of_agreesExcept allAg pre.machine.sse,
      Tf.ready.memory, Tf.ready.ready⟩,
    Tf.code, ipf, spf, ?_, ?_, allAg.grow, zero, ?_, ?_, ?_⟩
  · intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bfin.trans ((slots 32 (by omega)).trans atCopy.saved3)
    · exact allAg.read (r := 5) (n := 64) (by simp [appendPushChanges, appendBodyChanges,
        MemoryRoutines.callChanges,
        appendUpdateChanges, appendTailChanges])
    · exact r12fin.trans ((slots 24 (by omega)).trans atCopy.saved12)
    · exact allAg.read (r := 13) (n := 64) (by simp [appendPushChanges, appendBodyChanges,
        MemoryRoutines.callChanges,
        appendUpdateChanges, appendTailChanges])
    · exact r14fin.trans ((slots 16 (by omega)).trans atCopy.saved14)
    · exact r15fin.trans ((slots 8 (by omega)).trans atCopy.saved15)
  · exact allAg.directionFlagClear (by simp [appendPushChanges, appendBodyChanges,
      MemoryRoutines.callChanges, appendUpdateChanges, appendTailChanges]) pre.directionFlagUnset
  · have fc := append_memcpy_frame pre atCopy push result
    have fv := append_update_frame pre updateAg
    intro a ha
    refine (Tf.agrees.memory a (by simp [appendTailChanges, Component.Covers])).trans
      ((fv a ?_).trans (fc a ?_))
    · intro r hr
      have he : r = (⟨(s.regValue .rdi).toNat + 16, 8⟩ : MemoryRegion) := by simpa using hr
      subst r
      exact ha _ (by simp)
    · intro r hr
      have he : r = appendDestination buffer length ∨ r = Stack.region s 48 := by simpa using hr
      rcases he with rfl | rfl <;> exact ha _ (by simp)
  · exact Core.Absorb.word64At_keep word (fun i hi =>
      Tf.agrees.memory _ (by simp [appendTailChanges, Component.Covers]))
  · apply Core.Absorb.hasBytes_keep (append_memcpy_tag pre atCopy push result)
    intro i hi
    refine (Tf.agrees.memory _ (by simp [appendTailChanges, Component.Covers])).trans ?_
    apply append_update_keeps pre updateAg descDst
    have hb : buffer.toNat + length + 16 < 2 ^ 32 := pre.lengthBound
    change i < 16 at hi
    change buffer.toNat + length ≤ _ ∧ _ < buffer.toNat + length + 16
    simp only [appendDestination, BitVec.toNat_ofNat]
    omega

end ChaCha20Poly1305.Proofs.Encrypt
