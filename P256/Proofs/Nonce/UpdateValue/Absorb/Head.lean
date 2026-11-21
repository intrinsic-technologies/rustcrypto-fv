import P256.Proofs.Nonce.UpdateValue.Absorb.State
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem head [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (prepared : Prepared initial s state) :
    ∃ t, Advances boundary 4 s t ∧ Entered initial t state := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (add_r64_imm8_effect_step 0x10aaf3 0x48 0xc3 32
      (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep prepared.machine prepared.bindingsSupported)
      (programText_slice (programLoaded_codeIn prepared.loaded) 0xaaf3
        [0x48,0x83,0xc3,0x20] (by decide) (by decide +kernel)) prepared.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xaaf7 (by decide)))
  have agreesA : AgreesExcept [.reg 3, .flags, .rip] s a := effectA.agrees
  have memoryA := agreesA.external (by simp [Component.Covers])
  have rspA : stackPtr a = stackPtr s := agreesA.read (n := 64) (r := 4) (by simp)
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (movzx_r_m8_rex_effect_step 0x10aaf7 0x44 (by simp [RexPrefix]) 32
      (.inr rfl) (by intro; rfl) 7 (.sib 4 none 0 (.d32 231))
      (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (agreesA.codeIn (by simp [Component.Covers])
        (programLoaded_codeIn prepared.loaded)) 0xaaf7
        [0x44,0x0f,0xb6,0xbc,0x24,0xe7,0,0,0] (by decide) (by decide +kernel))
      ⟨effectA.rip, by
        change MemReadable a (stackPtr a + 231) 1
        rw [rspA]
        exact (ScalarFrame.stack_readable pre.callee prepared.toFrameState (by decide) (by decide)).of_external_eq memoryA⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xab00 (by decide)))
  have agreesB : AgreesExcept [.reg 15, .rip] a b := effectB.agrees
  have positionByte : s.external[stackPtr s + 231]? = some 0 := by
    have h := prepared.hmac.inner.position
    simp only [scratch, BitVec.add_assoc, BitVec.reduceAdd,
      ByteArray.size_append, HMAC.keyPad_size, ByteArray.size_empty,
      Nat.add_zero, Nat.reduceMod] at h
    rw [prepared.rsp]
    exact h
  have positionB : b.regValue .r15 = 0 := by
    have h := effectB.writes
    change b.regValue .r15 = (memLoad a.external (stackPtr a + 231) 8).setWidth 64 at h
    rw [rspA, memoryA, memLoad_8] at h
    change b.regValue .r15 = ((s.external[stackPtr s + 231]?).getD 0).toBitVec.setWidth 64 at h
    rw [positionByte] at h
    exact h
  have agreesAB := agreesA.trans agreesB
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (cmp_r64_imm8_effect_step 0x10ab00 0x49 0xff 31
      (by simp [RexWPrefix]) rfl rfl).advances readyB
      (programText_slice (agreesAB.codeIn (by simp [Component.Covers])
        (programLoaded_codeIn prepared.loaded)) 0xab00 [0x49,0x83,0xff,0x1f]
        (by decide) (by decide +kernel)) effectB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xab04 (by decide)))
  have agreesC : AgreesExcept [.flags, .rip] b c := effectC.agrees
  have agreesABC := agreesAB.trans agreesC
  obtain ⟨t, stepT, readyT, effectT⟩ := jcc_rel8_effect_step 0x10ab04 7 0x30 c readyC
    (programText_slice (agreesABC.codeIn (by simp [Component.Covers])
      (programLoaded_codeIn prepared.loaded)) 0xab04 [0x77,0x30]
      (by decide) (by decide +kernel)) ⟨effectC.rip, by intro; decide⟩
  have carry : (StatusFlags.ofRFLAGS c.RFLAGS).CF = true := by
    have h : (StatusFlags.ofRFLAGS c.RFLAGS).CF = (b.regValue .r15).ult 31 := effectC.flags.1
    rw [positionB] at h
    exact h
  have ripT : t.RIP = 0x10ab06 := by
    rw [effectT.rip]
    change (if !((StatusFlags.ofRFLAGS c.RFLAGS).CF ||
      (StatusFlags.ofRFLAGS c.RFLAGS).ZF) then 0x10ab36 else 0x10ab06) = _
    simp only [carry, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have runT : Advances boundary 1 c t := Advances.of_step stepT (.inl (by
    rw [ripT]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xab06 (by decide))))
  have agrees : AgreesExcept [.reg 3, .reg 15, .flags, .rip] s t := by
    apply (agreesABC.trans effectT.agrees).mono
    simp [jccEffect, X86Proofs.branchEffect, Effect.components]
  have memory := agrees.external (by simp [Component.Covers])
  have frame := prepared.toFrameState.after_registers readyT agrees
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, runA.trans (runB.trans (runC.trans runT)), frame, ripT, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((agreesB.trans (agreesC.trans effectT.agrees)).read (n := 64) (r := 3)
      (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])).trans
        (effectA.writes.trans (congrArg (· + 32) prepared.statePointer))
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans prepared.bufferPointer
  · exact ((agreesC.trans effectT.agrees).read (n := 64) (r := 15)
      (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])).trans positionB
  · simpa only [DrbgAt, memory] using prepared.drbg
  · exact prepared.hmac.copy (fun _ _ => by rw [memory])

end P256.Proofs.Nonce.UpdateValue.Absorb
