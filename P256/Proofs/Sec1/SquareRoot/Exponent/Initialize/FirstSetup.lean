import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.MoveStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LeaStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableValues

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem first_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (h : TableState s t x n)
    (rip : t.RIP=0x114f80) (ax : t.regValue .rax=exponentFrameBase s+0xc0) :
    ∃ u, Advances boundary 5 t u ∧ TableState s u x n ∧
      u.RIP=0x114f8f ∧
      u.regValue .rsi=exponentFrameBase s+0xc0 ∧
      u.regValue .rdx=exponentFrameBase s+0x2f8 ∧
      u.regValue .rdi=exponentFrameBase s+0x10 ∧
      u.regValue .rcx=s.regValue .rsi+32 ∧ u.regValue .r8=1 := by
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_move_r64 ctx.outerBoundary h.frame
    0x14f80 0x48 0xef (by simp [RexWPrefix]) rfl (by decide)
    rip (by decide) (by decide +kernel)
  have val1 := v1.trans h.output
  change AgreesExcept [.reg 7,.rip] t t1 at g1
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_move_r64 ctx.outerBoundary f1
    0x14f83 0x48 0xc6 (by simp [RexWPrefix]) rfl (by decide) ip1
    (by decide) (by decide +kernel)
  have val2 := v2.trans ((g1.read (n := 64) (r := 0) (by simp)).trans ax)
  change AgreesExcept [.reg 6,.rip] t1 t2 at g2
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_move_r64 ctx.outerBoundary f2
    0x14f86 0x48 0xda (by simp [RexWPrefix]) rfl (by decide)
    ip2 (by decide) (by decide +kernel)
  have val3 := v3.trans (((g1.trans g2).read (n := 64) (r := 3) (by simp)).trans h.input)
  change AgreesExcept [.reg 2,.rip] t2 t3 at g3
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_move_r64 ctx.outerBoundary f3
    0x14f89 0x4c 0xf9 (by simp [RexWPrefix]) rfl (by decide)
    ip3 (by decide) (by decide +kernel)
  have val4 := v4.trans ((((g1.trans g2).trans g3).read (n := 64) (r := 15) (by simp)).trans h.parameter)
  change AgreesExcept [.reg 1,.rip] t3 t4 at g4
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_move_r64 ctx.outerBoundary f4
    0x14f8c 0x4d 0xe8 (by simp [RexWPrefix]) rfl (by decide)
    ip4 (by decide) (by decide +kernel)
  have val5 := v5.trans (((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 13) (by simp)).trans h.negativeInverse)
  change AgreesExcept [.reg 8,.rip] t4 t5 at g5
  have state := h.of_agrees f5 ((((g1.trans g2).trans g3).trans g4).trans g5) (by simp) (by simp [Component.Covers])
  refine ⟨t5,((((a1.trans a2).trans a3).trans a4).trans a5),state,?_,?_,?_,?_,?_,val5⟩
  · exact ip5
  · exact (((g3.trans g4).trans g5).read (n := 64) (r := 6) (by simp)).trans val2
  · exact ((g4.trans g5).read (n := 64) (r := 2) (by simp)).trans val3
  · exact ((((g2.trans g3).trans g4).trans g5).read (n := 64) (r := 7) (by simp)).trans val1
  · exact (g5.read (n := 64) (r := 1) (by simp)).trans val4

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
