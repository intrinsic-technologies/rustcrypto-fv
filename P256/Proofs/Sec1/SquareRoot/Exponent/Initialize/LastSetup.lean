import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.MoveStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LeaStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableValues

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem last_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (h : TableState s t x 15)
    (rip : t.RIP=0x115364) :
    ∃ u, Advances boundary 6 t u ∧ TableState s u x 15 ∧
      u.RIP=0x115380 ∧
      u.regValue .rsi=exponentFrameBase s+0x260 ∧
      u.regValue .rdx=exponentFrameBase s+0x2f8 ∧
      u.regValue .rdi=exponentFrameBase s+0x10 ∧
      u.regValue .rcx=s.regValue .rsi+32 ∧ u.regValue .r8=1 ∧ exponentWordAt u (exponentFrameBase s+0x2c8) 1 := by
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_move_r64 ctx.outerBoundary h.frame
    0x15364 0x48 0xef (by simp [RexWPrefix]) rfl (by decide)
    rip (by decide) (by decide +kernel)
  have val1 := v1.trans h.output
  change AgreesExcept [.reg 7,.rip] t t1 at g1
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_lea_r64 ctx.outerBoundary f1
    0x15367 0x48 6 (.sib 4 none 0 (.d32 0x260))
    (by simp [RexWPrefix]) (by simp [AddrMode.Valid]) rfl rfl (by decide) ip1
    (by decide) (by decide +kernel)
  have val2 : t2.regValue .rsi=exponentFrameBase s+0x260 := by
    change t2.regValue .rsi=stackPtr t1+(0x260#32).signExtend 64 at v2
    rw [f1.rsp,show (0x260#32).signExtend 64=0x260#64 from rfl] at v2
    exact v2
  change AgreesExcept [.reg 6,.rip] t1 t2 at g2
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_move_r64 ctx.outerBoundary f2
    0x1536f 0x48 0xda (by simp [RexWPrefix]) rfl (by decide)
    ip2 (by decide) (by decide +kernel)
  have val3 := v3.trans (((g1.trans g2).read (n := 64) (r := 3) (by simp)).trans h.input)
  change AgreesExcept [.reg 2,.rip] t2 t3 at g3
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_move_r64 ctx.outerBoundary f3
    0x15372 0x4c 0xf9 (by simp [RexWPrefix]) rfl (by decide)
    ip3 (by decide) (by decide +kernel)
  have val4 := v4.trans ((((g1.trans g2).trans g3).read (n := 64) (r := 15) (by simp)).trans h.parameter)
  change AgreesExcept [.reg 1,.rip] t3 t4 at g4
  obtain ⟨saved,asaved,fsaved,ipsaved,vsaved,gsaved,msaved⟩ := frame_store_r64 ctx.toCalleePre f4
    0x15375 0x2c8 (.d32 0x2c8) 0x4c 5 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip4 (by decide) (by decide +kernel)
  have gregs := ((g1.trans g2).trans g3).trans g4
  have savedValue : exponentWordAt saved (exponentFrameBase s+0x2c8) 1 :=
    vsaved.trans ((gregs.read (n := 64) (r := 13) (by simp)).trans h.negativeInverse)
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_move_r64 ctx.outerBoundary fsaved
    0x1537d 0x4d 0xe8 (by simp [RexWPrefix]) rfl (by decide)
    ipsaved (by decide) (by decide +kernel)
  have val5 := v5.trans (((gregs.trans gsaved).read (n := 64) (r := 13) (by simp)).trans h.negativeInverse)
  change AgreesExcept [.reg 8,.rip] saved t5 at g5
  have state := h.of_agrees f5 ((gregs.trans gsaved).trans g5) (by simp) (by
    intro off ho c hc hv
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    obtain ⟨j,hj,eq⟩ := hv
    have apart : RangeApart (exponentFrameBase s+0x2c8#64) 8
        (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
      RangeApart.offsets (exponentFrameBase s) (by decide)
        (by unfold TableDataOffset at ho; omega) (by unfold TableDataOffset at ho; omega)
    apply apart j hj 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm)
  refine ⟨t5,(((((a1.trans a2).trans a3).trans a4).trans asaved).trans a5),state,?_,?_,?_,?_,?_,val5,?_⟩
  · exact ip5
  · exact ((((g3.trans g4).trans gsaved).trans g5).read (n := 64) (r := 6) (by simp)).trans val2
  · exact (((g4.trans gsaved).trans g5).read (n := 64) (r := 2) (by simp)).trans val3
  · exact (((((g2.trans g3).trans g4).trans gsaved).trans g5).read (n := 64) (r := 7) (by simp)).trans val1
  · exact ((gsaved.trans g5).read (n := 64) (r := 1) (by simp)).trans val4

  · change memLoad t5.external _ 64=1
    rw [m5]
    exact savedValue

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
