import P256.Proofs.Sec1.Affine.Uncompressed.Parse.YCopyMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.YFinalZeroMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.YFieldArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Interface
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Field
open Blocks

def ySelectSite : FieldCall.BinaryCallSite 3360 760 0x114380 128 := {
  codeOffset := 0x1081b
  disp := 0x3b60
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,152,312,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 664
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide }

theorem y_finished [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110790) (value : MontgomeryAt t (stackPtr s-592) (canonical x))
    (valid : t.regValue .r14 = if x < Operations.domain.p then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110820 ∧
      MontgomeryAt u (stackPtr s-312) (canonical x) ∧
      u.regValue .r14 = stackPtr s-312 ∧
      (∀ r ∈ [Syntax.Reg.rbx,Syntax.Reg.rbp,Syntax.Reg.r12,Syntax.Reg.r13,Syntax.Reg.r15], u.regValue r = t.regValue r) ∧
      u.external[stackPtr s-748]? = some (if x < Operations.domain.p then 1 else 0) := by
  obtain ⟨nc,c,rc,readyc,_,ec⟩ := y_copy_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10790 yCopyBytes
      (by decide) (by decide +kernel)) (y_copy_pre pre state rip)
  have fc := y_copy_frame pre state readyc ec
  have vc : MontgomeryAt c (stackPtr s-664) (canonical x) := by
    have h := y_copy_value pre state ec (x := canonical x) (by
      have addr : stackPtr t+168=stackPtr s-592 := stack_address state (by decide)
      rw [addr]
      exact value)
    have addr : stackPtr t+96=stackPtr s-664 := stack_address state (by decide)
    rwa [addr] at h
  have validc : c.regValue .r14 = if x < Operations.domain.p then 1 else 0 :=
    (ec.agrees.read (n := 64) (r := 14) (by simp [yCopyEffect,Effect.components])).trans valid
  obtain ⟨nz,z,rz,readyz,_,ez⟩ := y_final_zero_correct boundary pre.outerBoundary c readyc
    (programText_slice (programLoaded_codeIn fc.loaded) 0x107c4 yFinalZeroBytes
      (by decide) (by decide +kernel)) (y_final_zero_pre pre fc ec.rip)
  have fz := y_final_zero_frame pre fc readyz ez
  have zv : MontgomeryAt z (stackPtr s-152) 0 := by
    have h := y_final_zero_value pre fc ez
    have addr : stackPtr c+608=stackPtr s-152 := stack_address fc (by decide)
    rwa [addr] at h
  have vz : MontgomeryAt z (stackPtr s-664) (canonical x) := by
    apply vc.of_bytes_eq
    intro i hi
    have h := y_final_zero_byte ez (off := 96) (len := 32) (by decide) (by
      intro a n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
      omega) hi
    have addr : stackPtr c+96#64=stackPtr s-664 := stack_address fc (by decide)
    rwa [addr] at h
  obtain ⟨na,a,ra,readya,_,ea⟩ := y_field_arguments_correct boundary pre.outerBoundary z readyz
    (programText_slice (programLoaded_codeIn fz.loaded) 0x10803 yFieldArgumentsBytes
      (by decide) (by decide +kernel)) ez.rip
  have fa := fz.after_registers readya ea.agrees
    (by simp [yFieldArgumentsEffect,Effect.components,Component.Covers]) (by simp [yFieldArgumentsEffect,Effect.components])
  have ma := ea.agrees.external (by simp [yFieldArgumentsEffect,Effect.components,Component.Covers])
  have source : a.regValue .rsi=stackPtr s-152 := ea.writes.2.1.trans (stack_address fz (by decide))
  have right : a.regValue .rdx=stackPtr s-664 := ea.writes.2.2.1.trans (stack_address fz (by decide))
  have output : a.regValue .rdi=stackPtr s-312 := ea.writes.2.2.2.trans (stack_address fz (by decide))
  have ptr : a.regValue .r14=stackPtr s-312 := ea.writes.1.trans (stack_address fz (by decide))
  have choice : a.regValue .rcx=if decide (x < Operations.domain.p) then 1 else 0 := by
    have h : a.regValue .rcx = ((c.regValue .r14).setWidth 32).setWidth 64 :=
      (ea.agrees.read (n := 64) (r := 1) (by simp [yFieldArgumentsEffect,Effect.components])).trans ez.writes.2.2.2.2.2.2
    rw [h,validc]
    by_cases hx : x < Operations.domain.p <;> simp [hx]
  have zeroA := zv.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  have valueA := vz.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  obtain ⟨nf,u,rf,fu,iu,result,abi,kept,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun _ v => if decide (x < Operations.domain.p) then v else 0)
    pre.toCalleePre fa ySelectSite
    (fun entry hp hc left right => Projective.Multiply.Machine.Lookup.Select.field_select_correct
      hp left right (hc.trans choice)) ea.rip source right output zeroA valueA
  have result' : MontgomeryAt u (stackPtr s-312) (canonical x) := by
    change MontgomeryAt u (stackPtr s-312) (if decide (x < Operations.domain.p) then canonical x else 0) at result
    by_cases hx : x < Operations.domain.p
    · simpa only [hx,decide_true,Bool.true_eq,ite_true] using result
    · simpa only [canonical,hx,decide_false,Bool.false_eq_true,ite_false] using result
  refine ⟨nc+nz+na+nf,u,((rc.trans rz).trans ra).trans rf,fu,iu,result',
    (abi .r14 (by simp)).trans ptr,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (abi .rbx (by simp)).trans ((ea.agrees.read (n := 64) (r := 3)
        (by simp [yFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 3)
          (by simp [yFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 3)
            (by simp [yCopyEffect,Effect.components]))))
    · exact (abi .rbp (by simp)).trans ((ea.agrees.read (n := 64) (r := 5)
        (by simp [yFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 5)
          (by simp [yFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 5)
            (by simp [yCopyEffect,Effect.components]))))
    · exact (abi .r12 (by simp)).trans ((ea.agrees.read (n := 64) (r := 12)
        (by simp [yFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 12)
          (by simp [yFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 12)
            (by simp [yCopyEffect,Effect.components]))))
    · exact (abi .r13 (by simp)).trans ((ea.agrees.read (n := 64) (r := 13)
        (by simp [yFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 13)
          (by simp [yFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 13)
            (by simp [yCopyEffect,Effect.components]))))
    · exact (abi .r15 (by simp)).trans ((ea.agrees.read (n := 64) (r := 15)
        (by simp [yFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 15)
          (by simp [yFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 15)
            (by simp [yCopyEffect,Effect.components]))))
  · have flag : z.external[stackPtr s-748]? = some (if x < Operations.domain.p then 1 else 0) := by
      have readable := ScalarFrame.stack_readable pre.toCalleePre fc (offset := 12) (len := 4) (by decide) (by decide)
      have h := Bytes.of_memLoad (n := 32) (fun i hi => ez.agrees.grow _ (readable.mem i hi)) 0 (by decide)
      have w : memLoad z.external (stackPtr c+12) 32 = (c.regValue .r14).setWidth 32 := ez.writes.1
      change z.external[stackPtr c+12+BitVec.ofNat 64 0]? = some (storedByte (memLoad z.external (stackPtr c+12) 32) 0) at h
      rw [w,validc] at h
      have addr : stackPtr c+12=stackPtr s-748 := stack_address fc (by decide)
      rw [addr] at h
      by_cases hx : x < Operations.domain.p <;> simpa [hx,storedByte] using h
    have h := kept 748 1 (by decide) (by decide) (by decide) 0 (by decide)
    simp only [BitVec.add_zero] at h
    rw [ma] at h
    exact h.trans flag

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
