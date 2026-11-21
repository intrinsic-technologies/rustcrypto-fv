import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Table
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.CopyCall

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_arguments [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (rip : t.RIP=0x1153b9) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧ u.RIP=0x1153ce ∧
      u.regValue .rdi=stackPtr s-592 ∧ u.regValue .rsi=stackPtr s-1256 ∧
      u.regValue .rdx=512 ∧ AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] t u := by
  obtain ⟨a,a1,f1,ip1,v1,g1,m1⟩ := frame_lea_r64 ctx.outerBoundary frame
    0x153b9 0x48 7 (.sib 4 none 0 (.d32 0x338))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) rip
    (by decide) (by decide +kernel)
  change AgreesExcept [.reg 7,.rip] t a at g1
  have di : a.regValue .rdi=stackPtr s-592 := by
    change a.regValue .rdi=stackPtr t+0x338 at v1
    rw [frame.rsp] at v1
    exact v1.trans (by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl)
  obtain ⟨b,a2,f2,ip2,v2,g2,m2⟩ := frame_lea_r64 ctx.outerBoundary f1
    0x153c1 0x48 6 (.sib 4 none 0 (.d32 0xa0))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) ip1
    (by decide) (by decide +kernel)
  change AgreesExcept [.reg 6,.rip] a b at g2
  have si : b.regValue .rsi=stackPtr s-1256 := by
    change b.regValue .rsi=stackPtr a+0xa0 at v2
    rw [f1.rsp] at v2
    exact v2.trans (by simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl)
  obtain ⟨u,a3,ready,e⟩ := (mov_r32_imm32_effect_step 0x1153c9 0xba (by decide) 512).advances
    (readyToStep f2.machine f2.bindingsSupported)
    (programText_slice (programLoaded_codeIn f2.loaded) 0x153c9 _ (by decide) (by decide +kernel))
    ip2 (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153ce (by decide)))
  have g3 : AgreesExcept [.reg 2,.rip] b u := e.agrees
  refine ⟨u,(a1.trans a2).trans a3,f2.after_registers ready g3 (by simp [Component.Covers])
    (by simp),e.rip,((g2.trans g3).read (n := 64) (r := 7) (by simp)).trans di,
    (g3.read (n := 64) (r := 6) (by simp)).trans si,e.writes,?_⟩
  exact ((g1.trans g2).trans g3).mono (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; grind only)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
