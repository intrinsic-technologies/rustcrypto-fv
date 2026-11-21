import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.WindowState
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Indices
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Mask
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Enter
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.WindowMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_window [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (state : WindowReady s t x) :
    ∃ u, Advances boundary 44 t u ∧ Frame s u ∧ u.RIP=0x1154c5 ∧
      u.regValue .rbp=3 ∧ u.regValue .r14=16 ∧ u.regValue .rbx=3 ∧
      u.regValue .r13=15 ∧ u.regValue .r15=s.regValue .rsi+32 ∧
      u.regValue .r11=0xffffffffffffffff ∧ u.regValue .r12=0xffffffffffffffff ∧
      u.external=setupMemory s t.external := by
  obtain ⟨t1,a1,f1,ip1,bx1,w1,c1,g1⟩ := prepare_indices ctx state.frame.scalarFrame state.rip state.bitCount
  have p1 : t1.regValue .r15=s.regValue .rsi+32 :=
    (g1.read (n := 64) (r := 15) (by simp)).trans state.parameter
  obtain ⟨t2,a2,f2,ip2,g2,m2⟩ := copy_one ctx f1 ip1 p1
  have bx2 : t2.regValue .rbx=3 := (g2.read (n := 64) (r := 3) (by simp [oneCopyComponents])).trans bx1
  have w2 : t2.regValue .r13=15 := (g2.read (n := 64) (r := 13) (by simp [oneCopyComponents])).trans w1
  have p2 : t2.regValue .r15=s.regValue .rsi+32 := (g2.read (n := 64) (r := 15) (by simp [oneCopyComponents])).trans p1
  obtain ⟨t3,a3,f3,ip3,bp3,mod3,g3,m3⟩ := window_head ctx f2 ip2 bx2 w2 p2
  have p3 : t3.regValue .r15=s.regValue .rsi+32 := (g3.read (n := 64) (r := 15) (by simp)).trans p2
  obtain ⟨t4,a4,f4,ip4,g4,m4⟩ := initialize_modulus ctx f3 ip3 p3
  have c4 : t4.regValue .rcx=2 :=
    (((g2.trans g3).trans g4).read (n := 64) (r := 1) (by simp [oneCopyComponents])).trans c1
  obtain ⟨t5,a5,f5,ip5,mask5,g5⟩ := initialize_mask ctx f4 ip4 c4
  have m5 : t5.external=t4.external := g5.external (by simp [Component.Covers])
  have mod5 : t5.regValue .r11=0xffffffffffffffff := ((g4.trans g5).read (n := 64) (r := 11) (by simp)).trans mod3
  have p5 : t5.regValue .r15=s.regValue .rsi+32 := ((g4.trans g5).read (n := 64) (r := 15) (by simp)).trans p3
  have inv5 : t5.regValue .r12=0xffffffffffffffff :=
    (((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 12) (by simp [oneCopyComponents])).trans state.inverse
  have bx5 : t5.regValue .rbx=3 := (((g3.trans g4).trans g5).read (n := 64) (r := 3) (by simp)).trans bx2
  have w5 : t5.regValue .r13=15 := (((g3.trans g4).trans g5).read (n := 64) (r := 13) (by simp)).trans w2
  obtain ⟨t6,a6,f6,ip6,g6,m6⟩ := initialize_constants ctx f5 ip5 mask5 mod5 p5 inv5 bx5 w5
  have memory6 : t6.external=windowMemory s t.external := by
    rw [m6,m5,m4,m3,m2,g1.external (by simp [Component.Covers])]
    rfl
  obtain ⟨t7,a7,r7,e7⟩ := (jmp_rel8_effect_step 0x115484 0x13 (by decide)).advances
    (readyToStep f6.machine f6.bindingsSupported)
    (programText_slice (programLoaded_codeIn f6.loaded) 0x15484 _ (by decide) (by decide +kernel))
    ip6 (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15499 (by decide)))
  have g7 : AgreesExcept [.rip] t6 t7 := e7.agrees
  have f7 := f6.after_registers r7 g7 (by simp [Component.Covers]) (by simp)
  have memory7 : t7.external=windowMemory s t.external := (g7.external (by simp [Component.Covers])).trans memory6
  have bp7 : t7.regValue .rbp=4 :=
    ((((g4.trans g5).trans g6).trans g7).read (n := 64) (r := 5) (by simp)).trans bp3
  have bx7 : t7.regValue .rbx=3 := ((g6.trans g7).read (n := 64) (r := 3) (by simp)).trans bx5
  have window7 : (Operand.mem (exponentFrameBase s+0x78) : Operand 32).read t7=16 := by
    change memLoad t7.external _ 32=16
    rw [memory7]
    exact windowMemory_window s t.external
  obtain ⟨u,a8,f8,ip8,bp8,w8,g8,m8⟩ := enter_tail ctx f7 bp7 bx7 window7 e7.rip
  refine ⟨u,((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8,
    f8,ip8,bp8,w8,?_,?_,?_,?_,?_,?_⟩
  · exact (g8.read (n := 64) (r := 3) (by simp)).trans bx7
  · exact (((g6.trans g7).trans g8).read (n := 64) (r := 13) (by simp)).trans w5
  · exact (((g6.trans g7).trans g8).read (n := 64) (r := 15) (by simp)).trans p5
  · exact (((g6.trans g7).trans g8).read (n := 64) (r := 11) (by simp)).trans mod5
  · exact (((g6.trans g7).trans g8).read (n := 64) (r := 12) (by simp)).trans inv5
  · rw [m8,memory7]
    rfl

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
