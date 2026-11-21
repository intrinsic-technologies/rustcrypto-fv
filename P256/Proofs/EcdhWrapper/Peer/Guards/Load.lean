import P256.Proofs.EcdhWrapper.Guards

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem load [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬InProgram boundary.rip) (rip : s.RIP = 0x1069c0)
    (pointer : MemReadable s (s.regValue .r12+8) 8)
    (length : MemReadable s (s.regValue .r15+8) 8) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1069c9 ∧
      t.regValue .r12 = memLoad s.external (s.regValue .r12+8) 64 ∧
      t.regValue .rbp = memLoad s.external (s.regValue .r15+8) 64 ∧
      AgreesExcept [.reg 12,.reg 5,.rip] s t := by
  obtain ⟨a,ra,readyA,ea⟩ := (mov_r64_m64_effect_step 0x1069c0 0x4d
    (by simp [RexWPrefix]) 4 (.sib 12 none 0 (.d8 8)) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x69c0 _ (by decide) (by decide +kernel))
    ⟨rip,pointer⟩ (boundary_ne_program outside (inProgram_of_textOffset 0x69c5 (by decide)))
  have ga : AgreesExcept [.reg 12,.rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have base : a.regValue .r15 = s.regValue .r15 := ga.read (n := 64) (r := 15) (by simp)
  obtain ⟨t,rt,readyT,et⟩ := (mov_r64_m64_effect_step 0x1069c5 0x49
    (by simp [RexWPrefix]) 5 (.base 15 (.d8 8)) (by decide) rfl rfl).advances readyA
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0x69c5 _
      (by decide) (by decide +kernel)) ⟨ea.rip,by
        change MemReadable a (a.regValue .r15+8) 8
        refine ⟨by rw [base]; exact length.low,?_⟩
        intro i hi
        rw [ma,base]
        exact length.mem i hi⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x69c9 (by decide)))
  have gt : AgreesExcept [.reg 5,.rip] a t := et.agrees
  refine ⟨t,ra.trans rt,readyT,et.rip,
    (gt.read (n := 64) (r := 12) (by simp)).trans ea.writes,?_,(ga.trans gt).mono (by simp)⟩
  have v : t.regValue .rbp = memLoad a.external (a.regValue .r15+8) 64 := et.writes
  simpa only [ma,base] using v

end P256.Proofs.EcdhWrapper.Peer.Guards
