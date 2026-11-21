import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreWindow
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LeaStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LoadStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.InputMemory
import P256.Proofs.Common.Instructions.Lea32
import P256.Proofs.Sec1.SquareRoot.Parameters

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.Lea32 (lea_r32_effect_step leaR32Effect)

theorem window_head [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (rip : t.RIP=0x115412)
    (word : t.regValue .rbx=3) (window : t.regValue .r13=15)
    (parameter : t.regValue .r15=s.regValue .rsi+32) :
    ∃ u, Advances boundary 4 t u ∧ Frame s u ∧ u.RIP=0x115421 ∧
      u.regValue .rbp=4 ∧ u.regValue .r11=0xffffffffffffffff ∧
      AgreesExcept [.reg 5,.reg 0,.reg 11,.rip,.mem (exponentFrameBase s+120) 4] t u ∧
      u.external=memStore t.external (exponentFrameBase s+120) (16#32) := by
  obtain ⟨a,a1,f1,ip1,v1,g1,m1⟩ := frame_lea_r64 ctx.outerBoundary frame
    0x15412 0x48 5 (.base 3 (.d8 1)) (by simp [RexWPrefix]) (by decide)
    rfl rfl (by decide) rip (by decide) (by decide +kernel)
  change AgreesExcept [.reg 5,.rip] t a at g1
  have vbp : a.regValue .rbp=4 := by
    change a.regValue .rbp=t.regValue .rbx+1 at v1
    rw [word] at v1
    exact v1
  have wina : a.regValue .r13=15 := (g1.read (n := 64) (r := 13) (by simp)).trans window
  obtain ⟨b,a2,r2,e2⟩ := (lea_r32_effect_step 0x115416 0x41 (by simp [RexNoWPrefix])
      0 (.base 13 (.d8 1)) (by decide) rfl rfl).advances
    (readyToStep f1.machine f1.bindingsSupported)
    (programText_slice (programLoaded_codeIn f1.loaded) 0x15416 _ (by decide) (by decide +kernel))
    ip1 (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1541a (by decide)))
  have g2 : AgreesExcept [.reg 0,.rip] a b := e2.agrees
  have f2 := f1.after_registers r2 g2 (by simp [Component.Covers]) (by simp)
  have ax : b.regValue .rax=16 := by
    have h : b.regValue .rax=((a.regValue .r13+1).setWidth 32).setWidth 64 := e2.writes
    rw [wina] at h
    exact h
  obtain ⟨c,a3,f3,ip3,g3,m3⟩ := store_window ctx f2 e2.rip ax
  have param : c.regValue .r15=s.regValue .rsi+32 :=
    (((g1.trans g2).trans g3).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr (next : BitVec 64) : (AddrMode.base 15 .none).addr c next=s.regValue .rsi+32 := by
    change c.regValue .r15+0#64=_
    rwa [BitVec.add_zero]
  obtain ⟨u,a4,f4,ip4,v4,g4,m4⟩ := frame_load_r64 ctx.outerBoundary f3
    0x1541e 0x4d 3 (.base 15 .none) (by simp [RexWPrefix]) (by decide)
    rfl rfl (by decide) ip3 (by decide) (by decide +kernel)
    (by rw [addr]; exact input_readable ctx f3 (offset := 32) (by decide))
  change AgreesExcept [.reg 11,.rip] c u at g4
  have modulus : u.regValue .r11=0xffffffffffffffff := by
    rw [addr] at v4
    have h := (parameters_modulus ctx.residue.2).memLoad_limb 0 (by decide)
    change memLoad s.external ((s.regValue .rsi+32)+0#64) 64=_ at h
    rw [BitVec.add_zero] at h
    exact v4.trans ((input_memLoad_of_frame ctx f3 (offset := 32) (by decide)).trans h)
  refine ⟨u,((a1.trans a2).trans a3).trans a4,f4,ip4,
    (((g2.trans g3).trans g4).read (n := 64) (r := 5) (by simp)).trans vbp,modulus,?_,?_⟩
  · exact (((g1.trans g2).trans g3).trans g4).mono (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; grind only)
  · rw [m4,m3]
    exact congrArg (fun m ↦ memStore m _ (16#32)) (g2.external (by simp [Component.Covers]) |>.trans m1)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
