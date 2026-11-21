import P256.Proofs.Nonce.Initialize.Prepare.Length.Guards

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Length

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem setup [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107872) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x10787f ∧
      memLoad t.external (stackPtr s + 168) 64 = s.regValue .r9 ∧
      AgreesExcept [.mem (stackPtr s + 168) 8, .reg 7, .rip] s t := by
  obtain ⟨a, aa, ar, ae⟩ :=
    (mov_m64_r64_effect_step 0x107872 0x4c (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7872 _
        (by decide +kernel) (by decide +kernel))
      ⟨rip, stack_writable8 pre stage (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre stage.toFrameState
          (offset := 168) (len := 8) (codeOffset := 0x7872) (codeLen := 8)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x787a (by decide)))
  have ag : AgreesExcept [.mem (stackPtr s + 168) 8, .rip] s a := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, stackPtr] using ae.agrees
  have af := after_store pre stage aa ar ag (by decide)
  have value : memLoad a.external (stackPtr s + 168) 64 = s.regValue .r9 := ae.writes
  obtain ⟨t, ta, tr, te⟩ :=
    (mov_r32_imm32_effect_step 0x10787a 0xbf (by decide) 127).advances ar
      (programText_slice (programLoaded_codeIn af.loaded) 0x787a _
        (by decide +kernel) (by decide +kernel)) ae.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x787f (by decide)))
  have tg : AgreesExcept [.reg 7, .rip] a t := te.agrees
  refine ⟨t, af.after_registers ta tr tg (by simp [Component.Covers]) (by simp),
    te.rip, ?_, (ag.trans tg).mono (by simp)⟩
  rw [tg.external (by simp [Component.Covers])]
  exact value

end P256.Proofs.Nonce.Initialize.Prepare.Length
