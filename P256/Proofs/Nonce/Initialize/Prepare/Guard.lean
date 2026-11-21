import P256.Proofs.Nonce.Initialize.Prepare.Load
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

theorem length_guard [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (state : OrderLoaded initial s boundary orderAddress) (rip : s.RIP = 0x1077fe) :
    ∃ t, OrderLoaded initial t boundary orderAddress ∧ t.RIP = 0x107808 := by
  obtain ⟨u, a1, r1, e1⟩ :=
    (cmp_r64_imm8_effect_step 0x1077fe 0x49 0xfb 32
      (by simp [RexWPrefix]) rfl rfl).advances (readyToStep state.stage.machine state.stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.stage.loaded) 0x77fe _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7802 (by decide)))
  have g1 : AgreesExcept [.flags, .rip] s u := e1.agrees
  have f1 := state.stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (cmpSpec (s.regValue .r11) 32).ZF at h
    rw [state.length] at h
    exact h
  obtain ⟨t, step, ready, raw⟩ := jcc_rel32_effect_step 0x107802 7 0x472 u r1
    (programText_slice (programLoaded_codeIn f1.loaded) 0x7802 _
      (by decide +kernel) (by decide +kernel)) ⟨e1.rip, fun _ => by decide +kernel⟩
  have e2 := jccEffect_not_taken (show condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = false by
    change (!((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)) = false
    rw [zero]
    simp) raw
  have a2 : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [e2.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7808 (by decide))))
  have g2 : AgreesExcept [.rip] u t := e2.agrees
  have f2 := f1.after_registers a2 ready g2 (by simp [Component.Covers]) (by simp)
  have total := g1.trans g2
  refine ⟨t, ⟨⟨f2, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, e2.rip⟩
  · exact (total.read (n := 64) (r := 6) (by simp)).trans state.secret
  · have sp : stackPtr t = stackPtr s := total.read (n := 64) (r := 4) (by simp)
    rw [sp]
    rw [total.external (by simp [Component.Covers])]
    exact state.output
  · exact (total.read (n := 64) (r := 11) (by simp)).trans state.length
  · exact (total.read (n := 64) (r := 8) (by simp)).trans state.count
  · exact (total.read (n := 64) (r := 0) (by simp)).trans state.source
  · exact (total.read (n := 64) (r := 9) (by simp)).trans state.entropy
  · exact (total.read (n := 64) (r := 15) (by simp)).trans state.order0
  · exact (total.read (n := 64) (r := 14) (by simp)).trans state.order1
  · exact (total.read (n := 64) (r := 13) (by simp)).trans state.order2
  · exact (total.read (n := 64) (r := 5) (by simp)).trans state.order3

end P256.Proofs.Nonce.Initialize.Prepare
