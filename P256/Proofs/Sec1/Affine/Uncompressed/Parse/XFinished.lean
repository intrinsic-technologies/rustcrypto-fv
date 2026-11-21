import P256.Proofs.Sec1.Affine.Uncompressed.Parse.XCopyMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.XFinalZeroMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.XFieldArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Interface
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Field
open Blocks

def xSelectSite : FieldCall.BinaryCallSite 3360 760 0x114380 128 := {
  codeOffset := 0x109f5
  disp := 0x3986
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,512,280,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 592
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide }

theorem x_finished [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x11095f) (value : MontgomeryAt t (stackPtr s-384) (canonical x))
    (valid : t.regValue .r15 = if x < Operations.domain.p then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x1109fa ∧
      MontgomeryAt u (stackPtr s-280) (canonical x) ∧
      u.regValue .r13 = stackPtr s-280 ∧
      (∀ r ∈ [Syntax.Reg.rbx,Syntax.Reg.rbp,Syntax.Reg.r12,Syntax.Reg.r14,Syntax.Reg.r15], u.regValue r = t.regValue r) ∧
      (∀ off len : Nat, (off,len) ∈ [(312,32),(748,1)] → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  obtain ⟨nc,c,rc,readyc,_,ec⟩ := x_copy_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1095f xCopyBytes
      (by decide) (by decide +kernel)) (x_copy_pre pre state rip)
  have fc := x_copy_frame pre state readyc ec
  have vc : MontgomeryAt c (stackPtr s-592) (canonical x) := by
    have h := x_copy_value pre state ec (x := canonical x) (by
      have addr : stackPtr t+376=stackPtr s-384 := stack_address state (by decide)
      rw [addr]
      exact value)
    have addr : stackPtr t+168=stackPtr s-592 := stack_address state (by decide)
    rwa [addr] at h
  have validc : c.regValue .r15 = if x < Operations.domain.p then 1 else 0 :=
    (ec.agrees.read (n := 64) (r := 15) (by simp [xCopyEffect,Effect.components])).trans valid
  obtain ⟨nz,z,rz,readyz,_,ez⟩ := x_final_zero_correct boundary pre.outerBoundary c readyc
    (programText_slice (programLoaded_codeIn fc.loaded) 0x1099f xFinalZeroBytes
      (by decide) (by decide +kernel)) (x_final_zero_pre pre fc ec.rip)
  have fz := x_final_zero_frame pre fc readyz ez
  have zv : MontgomeryAt z (stackPtr s-512) 0 := by
    have h := x_final_zero_value pre fc ez
    have addr : stackPtr c+248=stackPtr s-512 := stack_address fc (by decide)
    rwa [addr] at h
  have vz : MontgomeryAt z (stackPtr s-592) (canonical x) := by
    apply vc.of_bytes_eq
    intro i hi
    have h := x_final_zero_byte ez (off := 168) (len := 32) (by decide) (by
      intro a n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
      omega) hi
    have addr : stackPtr c+168#64=stackPtr s-592 := stack_address fc (by decide)
    rwa [addr] at h
  obtain ⟨na,a,ra,readya,_,ea⟩ := x_field_arguments_correct boundary pre.outerBoundary z readyz
    (programText_slice (programLoaded_codeIn fz.loaded) 0x109d7 xFieldArgumentsBytes
      (by decide) (by decide +kernel)) ez.rip
  have fa := fz.after_registers readya ea.agrees
    (by simp [xFieldArgumentsEffect,Effect.components,Component.Covers]) (by simp [xFieldArgumentsEffect,Effect.components])
  have ma := ea.agrees.external (by simp [xFieldArgumentsEffect,Effect.components,Component.Covers])
  have source : a.regValue .rsi=stackPtr s-512 := ea.writes.2.1.trans (stack_address fz (by decide))
  have right : a.regValue .rdx=stackPtr s-592 := ea.writes.2.2.1.trans (stack_address fz (by decide))
  have output : a.regValue .rdi=stackPtr s-280 := ea.writes.2.2.2.1.trans (stack_address fz (by decide))
  have ptr : a.regValue .r13=stackPtr s-280 := ea.writes.1.trans (stack_address fz (by decide))
  have choice : a.regValue .rcx=if decide (x < Operations.domain.p) then 1 else 0 := by
    have validz : z.regValue .r15 = if x < Operations.domain.p then 1 else 0 :=
      (ez.agrees.read (n := 64) (r := 15) (by simp [xFinalZeroEffect,Effect.components])).trans validc
    have h : a.regValue .rcx = ((z.regValue .r15).setWidth 32).setWidth 64 := ea.writes.2.2.2.2
    rw [h,validz]
    by_cases hx : x < Operations.domain.p <;> simp [hx]
  have zeroA := zv.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  have valueA := vz.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  obtain ⟨nf,u,rf,fu,iu,result,abi,kept,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun _ v => if decide (x < Operations.domain.p) then v else 0)
    pre.toCalleePre fa xSelectSite
    (fun entry hp hc left right => Projective.Multiply.Machine.Lookup.Select.field_select_correct
      hp left right (hc.trans choice)) ea.rip source right output zeroA valueA
  have result' : MontgomeryAt u (stackPtr s-280) (canonical x) := by
    change MontgomeryAt u (stackPtr s-280) (if decide (x < Operations.domain.p) then canonical x else 0) at result
    by_cases hx : x < Operations.domain.p
    · simpa only [hx,decide_true,Bool.true_eq,ite_true] using result
    · simpa only [canonical,hx,decide_false,Bool.false_eq_true,ite_false] using result
  refine ⟨nc+nz+na+nf,u,((rc.trans rz).trans ra).trans rf,fu,iu,result',
    (abi .r13 (by simp)).trans ptr,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (abi .rbx (by simp)).trans ((ea.agrees.read (n := 64) (r := 3)
        (by simp [xFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 3)
          (by simp [xFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 3)
            (by simp [xCopyEffect,Effect.components]))))
    · exact (abi .rbp (by simp)).trans ((ea.agrees.read (n := 64) (r := 5)
        (by simp [xFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 5)
          (by simp [xFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 5)
            (by simp [xCopyEffect,Effect.components]))))
    · exact (abi .r12 (by simp)).trans ((ea.agrees.read (n := 64) (r := 12)
        (by simp [xFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 12)
          (by simp [xFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 12)
            (by simp [xCopyEffect,Effect.components]))))
    · exact (abi .r14 (by simp)).trans ((ea.agrees.read (n := 64) (r := 14)
        (by simp [xFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 14)
          (by simp [xFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 14)
            (by simp [xCopyEffect,Effect.components]))))
    · exact (abi .r15 (by simp)).trans ((ea.agrees.read (n := 64) (r := 15)
        (by simp [xFieldArgumentsEffect,Effect.components])).trans ((ez.agrees.read (n := 64) (r := 15)
          (by simp [xFinalZeroEffect,Effect.components])).trans (ec.agrees.read (n := 64) (r := 15)
            (by simp [xCopyEffect,Effect.components]))))
  · intro off len hp i hi
    have cases : (off=312 ∧ len=32) ∨ (off=748 ∧ len=1) := by simpa using hp
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [kept 312 32 (by decide) (by decide) (by decide) i hi,ma]
      have hz := x_final_zero_byte ez (off := 448) (len := 32) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have az : stackPtr c+448#64=stackPtr s-312 := stack_address fc (by decide)
      rw [az] at hz
      have hc := x_copy_byte ec (off := 448) (len := 32) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have ac : stackPtr t+448#64=stackPtr s-312 := stack_address state (by decide)
      rw [ac] at hc
      exact hz.trans hc
    · rw [kept 748 1 (by decide) (by decide) (by decide) i hi,ma]
      have hz := x_final_zero_byte ez (off := 12) (len := 1) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have az : stackPtr c+12#64=stackPtr s-748 := stack_address fc (by decide)
      rw [az] at hz
      have hc := x_copy_byte ec (off := 12) (len := 1) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have ac : stackPtr t+12#64=stackPtr s-748 := stack_address state (by decide)
      rw [ac] at hc
      exact hz.trans hc

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
