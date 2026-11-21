import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Projective.Add.Frame.Restore
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem epilogue (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d4cd)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ fuel u, Advances boundary fuel t u ∧ CalleeResult s u boundary 65 4584 ∧
      u.external = t.external := by
  obtain ⟨a,runA,readyA,ea⟩ :=
    (mov_r64_r64_effect_step 0x10d4cd 0x4c 0xf8 (by simp [RexWPrefix]) rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xd4cd _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4d0 (by decide)))
  change (movR64R64Effect 0x10d4cd 0 15 t).Holds t a at ea
  have fa := after_registers frame readyA ea.agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨b,runB,readyB,eb⟩ :=
    (add_r64_imm32_effect_step 0x10d4d0 0x48 0xc4 2232 (by simp [RexWPrefix]) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0xd4d0 _ (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4d7 (by decide)))
  change (addR64Imm32Effect 0x10d4d0 4 2232 a).Holds a b at eb
  have ag : AgreesExcept [.reg 0,.reg 4,.flags,.rip] t b :=
    (ea.agrees.trans eb.agrees).mono (by simp)
  have memory : b.external = t.external := ag.external (by simp [Component.Covers])
  have sp : stackPtr b = stackPtr s-48 := by
    have h : stackPtr b = stackPtr a+2232 := eb.writes
    rw [h,fa.rsp]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have fb : ScalarFrame.FrameState s b 65 4584 48 :=
    ⟨bindingsSupported_of_ready_agrees frame.bindingsSupported readyB ag,
      supportedMachine_of_ready_agrees frame.machine readyB ag,
      (fun a b h => by rw [memory]; exact frame.loaded a b h),
      ag.directionFlagClear (by simp) frame.directionFlag,
      (fun a ha => ag.grow a (frame.allocated a ha)),
      (fun a ha => by rw [memory]; exact frame.frame a ha),sp,
      (fun entry he => by rw [memory]; exact frame.saved entry he),
      (by change memLoad b.external _ 64 = _; rw [memory]; exact frame.returnAddress),
      (ag.mxcsr (by simp)).trans frame.mxcsr,(ag.fcw (by simp)).trans frame.fp87⟩
  have code : Projective.Add.RestoreCode 0xd4d7 := by
    constructor <;> decide +kernel
  obtain ⟨u,runU,readyU,agu,ipu,spu,saved⟩ := Projective.Add.restore_registers
    pre.toCalleePre (by decide) fb code eb.rip
  have total := ag.trans agu
  have memU : u.external = t.external :=
    (agu.external (by simp [Projective.Add.restoreComponents,Component.Covers])).trans memory
  obtain ⟨n,run⟩ := execution
  exact ⟨9,u,(runA.trans runB).trans runU,
    ⟨⟨n+9,by simpa only [Nat.add_assoc] using ((run.trans runA).trans runB).trans runU⟩,
      ipu,spu,bindingsSupported_of_ready_agrees frame.bindingsSupported readyU total,
      supportedMachine_of_ready_agrees frame.machine readyU total,saved,
      total.directionFlagClear (by simp [Projective.Add.restoreComponents]) frame.directionFlag,
      (total.mxcsr (by simp [Projective.Add.restoreComponents])).trans frame.mxcsr,
      (total.fcw (by simp [Projective.Add.restoreComponents])).trans frame.fp87,
      (fun a ha => by rw [memU]; exact frame.frame a ha),
      (fun a b hb => by rw [memU]; exact frame.loaded a b hb),
      (fun a ha => total.grow a (frame.allocated a ha))⟩,memU⟩

end P256.Proofs.Signing.Core.Iteration.Output
