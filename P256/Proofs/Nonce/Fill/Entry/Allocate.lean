import P256.Proofs.Nonce.Fill.Interface
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem allocate [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {state : State} (pre : Pre initial boundary orderAddress state) :
    ∃ t, Advances boundary 7 initial t ∧ Frame initial t ∧ t.RIP = 0x107341 ∧
      AgreesExcept (saveFrame initial ++ [.flags]) initial t := by
  obtain ⟨s, runS, readyS, loadedS, ripS, rspS, memoryS, agreesS⟩ :=
    save_registers pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha hp)
      pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide) (codeOffset := 0x7330) pre.rip (by constructor <;> decide +kernel)
  obtain ⟨t, runT, readyT, effect⟩ :=
    (sub_r64_imm32_effect_step 0x10733a 0x48 0xec 184
      (by simp [RexWPrefix]) rfl rfl).advances readyS
      (programText_slice (programLoaded_codeIn loadedS) 0x733a _
        (by decide) (by decide +kernel)) ripS
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7341 (by decide)))
  have agreesT : AgreesExcept [.reg 4, .flags, .rip] s t := effect.agrees
  have memoryT := agreesT.external (by simp [Component.Covers])
  have agrees : AgreesExcept (saveFrame initial ++ [.flags]) initial t :=
    (agreesS.trans agreesT).mono (by simp [saveFrame])
  have loaded : ProgramLoaded t := by
    intro a b hb
    rw [memoryT]
    exact loadedS a b hb
  have rsp : stackPtr t = stackPtr initial - 232 := by
    have h : stackPtr t = stackPtr s - 184 := effect.writes
    rw [h, rspS, BitVec.sub_sub]
    rfl
  have frame := ScalarFrame.prologue_frame pre.toCalleePre (by decide) readyT loaded rsp
    (memoryT.trans memoryS) agrees
  refine ⟨t, runS.trans runT, ?_, effect.rip, agrees⟩
  refine ⟨frame.bindingsSupported, frame.machine, frame.loaded, frame.directionFlag,
    frame.allocated, ?_, frame.rsp, frame.saved, frame.returnAddress, frame.mxcsr, frame.fp87⟩
  intro a ha
  apply frame.frame a
  intro r hr
  apply ha r
  have hr : r = registerRegion initial .rdi 72 ∨ r = Stack.region initial 2096 := by simpa using hr
  rcases hr with rfl | rfl <;> simp [regions]

end P256.Proofs.Nonce.Fill.Entry
