import P256.Proofs.Sec1.Affine.Compressed.Setup
import P256.Proofs.Sec1.Affine.Compact.Compare.Memory
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Compare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tail [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (frame : Frame s t) (rip : t.RIP=0x1104d8)
    (q : BitVec 64) (hq : q=0 ∨ q=1) (value : memLoad t.external (stackPtr s-512) 64=q) :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP=0x1104ea ∧
      u.regValue .rax=q ∧ AgreesExcept (clobbers s) t u := by
  have addr : (AddrMode.sib 4 none 0 (.d32 248)).addr t 0x1104e0=stackPtr s-512 := by
    change stackPtr t+248#64=_
    rw [frame.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have read : MemReadable t (stackPtr s-512) 1 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre frame
      (offset := 248) (len := 1) (by decide) (by decide)
    rwa [ScalarFrame.scalar_stack_address frame.rsp (by decide) (by decide)] at h
  obtain ⟨a,a1,r1,e1⟩ := (movzx_r32_m8_effect_step 0x1104d8 0
    (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl).advances
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x104d8 _ (by decide) (by decide +kernel))
    ⟨rip,addr ▸ read⟩ (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104e0 (by decide)))
  have g1 : AgreesExcept [.reg 0,.rip] t a := e1.agrees
  have f1 := frame.after_registers r1 g1 (by simp [Component.Covers]) (by simp)
  have ax : a.regValue .rax=q := by
    have h := e1.writes
    change a.regValue .rax=(memLoad t.external ((AddrMode.sib 4 none 0 (.d32 248)).addr t 0x1104e0) 8).setWidth 64 at h
    rw [addr,← Common.Field.SquareRoot.memLoad_setWidth_of_le t.external _ (m := 64) (by decide) (by decide),value] at h
    rcases hq with rfl | rfl <;> exact h
  obtain ⟨b,a2,r2,g2,ip2,di⟩ := Generate.Zero.mask_arguments boundary 0x1104e0 r1
    (programText_slice (programLoaded_codeIn f1.loaded) 0x104e0 _ (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104e2 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104e5 (by decide)))
  have f2 := f1.after_registers r2 g2 (by simp [Component.Covers]) (by simp)
  have db : b.regValue .rdi=q := by
    rw [di,ax]
    rcases hq with rfl | rfl <;> rfl
  obtain ⟨u,a3,f3,ip3,ax3,g3⟩ := Compressed.choice pre f2 0x104e5 0x8b86
    (by decide) (by decide +kernel) (by decide) ip2
  refine ⟨u,(a1.trans a2).trans a3,f3,ip3,?_,?_⟩
  · rw [ax3,db]
    rcases hq with rfl | rfl <;> rfl
  · exact ((g1.trans g2).trans g3).mono (by simp [clobbers,ScalarFrame.choiceClobbers])

end P256.Proofs.Sec1.Affine.Compact.Compare
