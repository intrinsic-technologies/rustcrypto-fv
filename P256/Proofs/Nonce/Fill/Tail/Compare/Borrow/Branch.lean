import P256.Proofs.Nonce.Fill.Tail.Compare.Borrow.Frame
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.CompareByteMemory
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Borrow

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Common.Instructions.CompareByteMemory

open Classical in
theorem branch [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Fill.Pre initial boundary orderAddress original)
    (input : Compared initial s orderAddress state) (rip : s.RIP = 0x1076b6)
    (choice : (s.regValue .rax).setWidth 8 &&& 1 =
      if ValidNonce (nextCandidate state).1 then 1 else 0) :
    ∃ t, Advances boundary 4 s t ∧ Compared initial t orderAddress state ∧
      t.RIP = if ValidNonce (nextCandidate state).1 then 0x1076e5 else 0x1076c3 := by
  obtain ⟨a, runA, readyA, effectA⟩ := (and_al_imm8_effect_step 0x1076b6 1).advances
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x76b6 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76b8 (by decide)))
  have agreesA : AgreesExcept [.reg 0, .flags, .rip] s a := effectA.agrees
  have inputA := input.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have valueA : (a.regValue .rax).setWidth 8 =
      if ValidNonce (nextCandidate state).1 then 1 else 0 := by
    have h := congrArg (BitVec.setWidth 8) effectA.writes
    change (a.regValue .rax).setWidth 8 =
      (mergeGPR 8 ((s.regValue .rax).setWidth 8 &&& 1) (s.regValue .rax)).setWidth 8 at h
    rw [mergeGPR_low8, choice] at h
    exact h
  have writable : MemWritable a (stackPtr a + 8) 1 := by
    have h : MemWritable a (stackPtr a + 8) 8 :=
      stack_writable8 pre inputA.toFrame (offset := 8) (by decide) (by decide)
    exact ⟨by have := h.low; omega,
      fun i hi => h.mem i (by omega), by have := h.tables; omega⟩
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (mov_m8_r8_legacy_effect_step 0x1076b8 0 (by decide)
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn inputA.loaded) 0x76b8 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, writable, stack_code pre inputA.toFrame
        (offset := 8) (len := 1) (codeOffset := 0x76b8) (codeLen := 4) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76bc (by decide)))
  have agreesB : AgreesExcept [.mem (stackPtr a + 8) 1, .rip] a b := by
    simpa [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, stackPtr, Operand.read_reg64] using effectB.agrees
  have inputB := after_stack pre inputA readyB agreesB (offsets := [8]) (by
    intro c member addr cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cover
      exact ⟨8, by simp, i, by omega, by rw [inputA.rsp]; rfl⟩
    · exact cover.elim)
    (by intro off member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; subst off; decide)
    (by simp) (by simp) (by simp)
  have stored : memLoad b.external (stackPtr b + 8) 8 =
      if ValidNonce (nextCandidate state).1 then 1 else 0 := by
    have h : memLoad b.external (stackPtr a + 8) 8 = (a.regValue .rax).setWidth 8 := effectB.writes
    rw [inputA.rsp, ← inputB.rsp] at h
    exact h.trans valueA
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (CompareByteMemory.cmp_m8_imm8_effect_step 0x1076bc (.sib 4 none 0 (.d8 8))
      (by decide +kernel) rfl rfl 0).advances readyB
      (programText_slice (programLoaded_codeIn inputB.loaded) 0x76bc _
        (by decide) (by decide +kernel))
      ⟨effectB.rip, stack_readable pre inputB.toFrame (offset := 8) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76c1 (by decide)))
  have agreesC : AgreesExcept [.flags, .rip] b c := effectC.agrees
  have inputC := inputB.after_registers readyC agreesC
    (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have flag : (StatusFlags.ofRFLAGS c.RFLAGS).ZF =
      if ValidNonce (nextCandidate state).1 then false else true := by
    have h := effectC.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF =
      ((memLoad b.external (stackPtr b + 8) 8 - 0) == 0) at h
    rw [stored] at h
    by_cases valid : ValidNonce (nextCandidate state).1 <;> simpa [valid] using h
  have target : (jccEffect 0x1076c1 2 5 ((0x22 : BitVec 8).signExtend 64) c).rip =
      if ValidNonce (nextCandidate state).1 then 0x1076e5 else 0x1076c3 := by
    change (if (!(StatusFlags.ofRFLAGS c.RFLAGS).ZF) = true then 0x1076e5 else 0x1076c3) = _
    rw [flag]
    split <;> rfl
  obtain ⟨t, runT, readyT, effectT⟩ := (jcc_rel8_effect_step 0x1076c1 5 0x22).advances readyC
    (programText_slice (programLoaded_codeIn inputC.loaded) 0x76c1 _
      (by decide) (by decide +kernel))
    ⟨effectC.rip, by intro; decide +kernel⟩ (by
      rw [target]
      split
      · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76e5 (by decide))
      · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76c3 (by decide)))
  have agreesT : AgreesExcept [.rip] c t := effectT.agrees
  exact ⟨t, ((runA.trans runB).trans runC).trans runT,
    inputC.after_registers readyT agreesT (by simp [Component.Covers]) (by simp) (by simp) (by simp),
    effectT.rip.trans target⟩

end P256.Proofs.Nonce.Fill.Tail.Compare.Borrow
