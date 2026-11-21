import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks.Setup
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks.Equality
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks.Choice
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.MovzxByte

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem check [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (which : Bool) (rip : t.RIP = if which then 0x1099c5 else 0x10997d)
    (first : Nat256At t (stackPtr t + 64#64) x)
    (second : Nat256At t (stackPtr t + 96#64) y) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if which then 0x109a09 else 0x1099c1) ∧
      u.regValue .rax = (if (if which then y else x) = 0 then 1 else 0) ∧
      Nat256At u (stackPtr u + 64#64) x ∧ Nat256At u (stackPtr u + 96#64) y := by
  obtain ⟨a, ast, arip, adi, adx, asi, acx, zero, ax, ay⟩ := setup pre state which rip first second
  let d := if which then y else x
  have scalar : Nat256At a (stackPtr a + BitVec.ofNat 64 (if which then 96 else 64)) d := by
    cases which
    · exact ax
    · exact ay
  obtain ⟨v, vst, vrip, value, preserve⟩ := equal_call pre ast
    (if which then 0x99fa else 0x99b2) (if which then 0xf871 else 0xf8b9)
    (by cases which <;> decide) (by cases which <;> decide +kernel)
    (by cases which <;> decide +kernel) (by cases which <;> exact arip)
    adi adx asi acx (by cases which <;> decide) scalar zero
  have vx := preserve 64 x (by decide) ax
  have vy := preserve 96 y (by decide) ay
  let andOffset : Nat := if which then 0x99ff else 0x99b7
  let p : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 andOffset
  obtain ⟨b, hb, rb, eb⟩ :=
    (P256.Proofs.Common.Instructions.ByteOps.ByteOps.and_al_imm8_effect_step p 1).advances
      (readyToStep vst.machine vst.bindingsSupported)
      (programText_slice (programLoaded_codeIn vst.loaded) andOffset _
        (by cases which <;> decide) (by cases which <;> decide +kernel))
      (by cases which <;> exact vrip)
      (by cases which
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x99b9 (by decide))
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a01 (by decide)))
  have fb : AgreesExcept [.reg 0, .flags, .rip] v b := eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have al : (Operand.reg 0 : Operand 8).read b = if d = 0 then 1 else 0 := by
    have h := eb.writes
    change b.regValue .rax = mergeGPR 8 ((v.regValue .rax).setWidth 8 &&& 1) (v.regValue .rax) at h
    change (b.regValue .rax).setWidth 8 = _
    rw [h, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, value]
    split <;> decide +kernel
  have movCode := programText_slice ((programLoaded_codeIn vst.loaded).of_external_eq mb)
    (andOffset + 2) [0x0f,0xb6,0xf8] (by cases which <;> decide)
    (by cases which <;> decide +kernel)
  obtain ⟨c, hc, rc, ec⟩ :=
    (P256.Proofs.Common.Instructions.MovzxByte.movzx_r32_r8_effect_step (p + 2#64) 0xf8
      (by decide) (by decide)).advances rb
      (by simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using movCode) eb.rip
      (by cases which
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x99bc (by decide))
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a04 (by decide)))
  have fc : AgreesExcept [.reg 7, .rip] b c := ec.agrees
  have f : AgreesExcept [.reg 0, .reg 7, .flags, .rip] v c := (fb.trans fc).mono (by simp)
  have cst := vst.after_registers (hb.trans hc) rc f (by simp [Component.Covers]) (by simp)
  have cdi : c.regValue .rdi = if d = 0 then 1 else 0 := by
    have h : c.regValue .rdi = ((Operand.reg 0 : Operand 8).read b).setWidth 64 := ec.writes
    rw [h, al]
    split <;> decide +kernel
  have spc : stackPtr c = stackPtr v := f.read (n := 64) (r := 4) (by simp)
  have mc := f.external (by simp [Component.Covers])
  have cx : Nat256At c (stackPtr c + 64#64) x := by
    simpa only [Nat256At, mc, spc] using vx
  have cy : Nat256At c (stackPtr c + 96#64) y := by
    simpa only [Nat256At, mc, spc] using vy
  obtain ⟨u, ust, urip, uax, uf⟩ := choice_call pre cst
    (if which then 0x9a04 else 0x99bc) (if which then 0xf667 else 0xf6af)
    (by cases which <;> decide) (by cases which <;> decide +kernel)
    (by cases which <;> decide +kernel) (by cases which <;> exact ec.rip)
  have spu : stackPtr u = stackPtr c := ust.rsp.trans cst.rsp.symm
  refine ⟨u, ust, ?_, ?_, ?_, ?_⟩
  · cases which <;> exact urip
  · rw [uax]
    change ((c.regValue .rdi).setWidth 8).setWidth 64 = _
    rw [cdi]
    split <;> decide +kernel
  · rw [spu]
    exact choice_scalar cst.toFrame uf (off := 64) (by decide) cx
  · rw [spu]
    exact choice_scalar cst.toFrame uf (off := 96) (by decide) cy

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks
