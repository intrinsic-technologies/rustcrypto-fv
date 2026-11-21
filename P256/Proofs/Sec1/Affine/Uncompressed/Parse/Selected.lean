import P256.Proofs.Sec1.Affine.Uncompressed.Parse.LimbCall
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.YZeroMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.XZeroMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.YLimbArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.XLimbArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Field
open Blocks

theorem y_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110739)
    (valid : t.regValue .rax = if x < Operations.domain.p then 1 else 0)
    (value : MontgomeryAt t (stackPtr s-744) (x % Operations.domain.p))
    : ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110790 ∧
      MontgomeryAt u (stackPtr s-592) (canonical x) ∧
      u.regValue .r14 = (if x < Operations.domain.p then 1 else 0) ∧
      (∀ r ∈ [Syntax.Reg.rbx,Syntax.Reg.rbp,Syntax.Reg.r12,Syntax.Reg.r13,Syntax.Reg.r15], u.regValue r = t.regValue r) ∧
      (∀ off len : Nat, (off,len) ∈ [(312,32),(748,1)] → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  obtain ⟨nz,z,rz,readyz,_,ez⟩ := y_zero_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10739 yZeroBytes
      (by decide) (by decide +kernel)) (y_zero_pre pre state rip)
  have fz := y_zero_frame pre state readyz ez
  have zero := y_zero_value pre state ez
  have zd : stackPtr t+168 = stackPtr s-592 := stack_address state (by decide)
  rw [zd] at zero
  have candidate : MontgomeryAt z (stackPtr s-744) (x % Operations.domain.p) := by
    apply value.of_bytes_eq
    intro i hi
    have h := y_zero_byte ez (off := 16) (len := 32) (by decide) (by
      intro a n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
      omega) hi
    have addr : stackPtr t+16#64 = stackPtr s-744 := stack_address state (by decide)
    rw [addr] at h
    exact h
  have vz : z.regValue .rax = if x < Operations.domain.p then 1 else 0 :=
    (ez.agrees.read (n := 64) (r := 0) (by simp [yZeroEffect,Effect.components])).trans valid
  obtain ⟨na,a,ra,readya,_,ea⟩ := y_limb_arguments_correct boundary pre.outerBoundary z readyz
    (programText_slice (programLoaded_codeIn fz.loaded) 0x1076d yLimbArgumentsBytes
      (by decide) (by decide +kernel)) ez.rip
  have fa := fz.after_registers readya ea.agrees
    (by simp [yLimbArgumentsEffect, Effect.components, Component.Covers]) (by simp [yLimbArgumentsEffect, Effect.components])
  have ma := ea.agrees.external (by simp [yLimbArgumentsEffect, Effect.components, Component.Covers])
  have source : a.regValue .rdx = stackPtr s-744 :=
    ea.writes.2.2.2.2.1.trans (stack_address fz (by decide))
  have output : a.regValue .rdi = stackPtr s-592 :=
    ea.writes.2.1.trans (stack_address fz (by decide))
  have choice : a.regValue .r8 = if decide (x < Operations.domain.p) then 1 else 0 := by
    have h : a.regValue .r8 = ((z.regValue .rax).setWidth 8).setWidth 64 := ea.writes.2.2.2.2.2
    rw [h,vz]
    by_cases hx : x < Operations.domain.p <;> simp [hx]
  have chosen : a.regValue .r14 = if x < Operations.domain.p then 1 else 0 := by
    have h : a.regValue .r14 = ((z.regValue .rax).setWidth 8).setWidth 64 := ea.writes.1
    rw [h,vz]
    by_cases hx : x < Operations.domain.p <;> simp [hx]
  have zeroA := zero.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  have valueA := candidate.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  obtain ⟨nc,u,rc,fu,iu,result,abi,kept,_⟩ := limb_call pre fa (out := 592) (by decide) (by decide)
    0x1078b 0x8a30 (by decide) (by decide +kernel) (by decide) ea.rip
    ⟨ea.writes.2.2.1,ea.writes.2.2.2.1⟩ source output zeroA valueA choice
  have result' : MontgomeryAt u (stackPtr s-592) (canonical x) := by
    by_cases hx : x < Operations.domain.p
    · simpa only [BitVec.ofNat_eq_ofNat,hx,decide_true,Bool.true_eq,ite_true,canonical,Nat.mod_eq_of_lt hx] using result
    · simpa only [BitVec.ofNat_eq_ofNat,hx,decide_false,Bool.false_eq_true,ite_false,canonical] using result
  refine ⟨nz+na+nc,u,(rz.trans ra).trans rc,fu,iu,result',
    (abi .r14 (by simp)).trans chosen,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (abi .rbx (by simp)).trans ((ea.agrees.read (n := 64) (r := 3)
        (by simp [yLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 3) (by simp [yZeroEffect,Effect.components])))
    · exact (abi .rbp (by simp)).trans ((ea.agrees.read (n := 64) (r := 5)
        (by simp [yLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 5) (by simp [yZeroEffect,Effect.components])))
    · exact (abi .r12 (by simp)).trans ((ea.agrees.read (n := 64) (r := 12)
        (by simp [yLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 12) (by simp [yZeroEffect,Effect.components])))
    · exact (abi .r13 (by simp)).trans ((ea.agrees.read (n := 64) (r := 13)
        (by simp [yLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 13) (by simp [yZeroEffect,Effect.components])))
    · exact (abi .r15 (by simp)).trans ((ea.agrees.read (n := 64) (r := 15)
        (by simp [yLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 15) (by simp [yZeroEffect,Effect.components])))
  · intro off len hp i hi
    have cases : (off=312 ∧ len=32) ∨ (off=748 ∧ len=1) := by simpa using hp
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [kept 312 32 (by decide) (by decide) (by decide) i hi, ma]
      have h := y_zero_byte ez (off := 448) (len := 32) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have addr : stackPtr t+448#64=stackPtr s-312 := stack_address state (by decide)
      rwa [addr] at h
    · rw [kept 748 1 (by decide) (by decide) (by decide) i hi, ma]
      have h := y_zero_byte ez (off := 12) (len := 1) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have addr : stackPtr t+12#64=stackPtr s-748 := stack_address state (by decide)
      rwa [addr] at h

theorem x_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x11090a)
    (valid : t.regValue .rax = if x < Operations.domain.p then 1 else 0)
    (value : MontgomeryAt t (stackPtr s-744) (x % Operations.domain.p))
    (sourceRegister : t.regValue .r12 = stackPtr s-744)
    : ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11095f ∧
      MontgomeryAt u (stackPtr s-384) (canonical x) ∧
      u.regValue .r15 = (if x < Operations.domain.p then 1 else 0) ∧
      (∀ r ∈ [Syntax.Reg.rbx,Syntax.Reg.rbp,Syntax.Reg.r12,Syntax.Reg.r13,Syntax.Reg.r14], u.regValue r = t.regValue r) ∧
      (∀ off len : Nat, (off,len) ∈ [(312,32),(748,1)] → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  obtain ⟨nz,z,rz,readyz,_,ez⟩ := x_zero_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1090a xZeroBytes
      (by decide) (by decide +kernel)) (x_zero_pre pre state rip)
  have fz := x_zero_frame pre state readyz ez
  have zero := x_zero_value pre state ez
  have zd : stackPtr t+376 = stackPtr s-384 := stack_address state (by decide)
  rw [zd] at zero
  have candidate : MontgomeryAt z (stackPtr s-744) (x % Operations.domain.p) := by
    apply value.of_bytes_eq
    intro i hi
    have h := x_zero_byte ez (off := 16) (len := 32) (by decide) (by
      intro a n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
      omega) hi
    have addr : stackPtr t+16#64 = stackPtr s-744 := stack_address state (by decide)
    rw [addr] at h
    exact h
  have vz : z.regValue .rax = if x < Operations.domain.p then 1 else 0 :=
    (ez.agrees.read (n := 64) (r := 0) (by simp [xZeroEffect,Effect.components])).trans valid
  obtain ⟨na,a,ra,readya,_,ea⟩ := x_limb_arguments_correct boundary pre.outerBoundary z readyz
    (programText_slice (programLoaded_codeIn fz.loaded) 0x1093e xLimbArgumentsBytes
      (by decide) (by decide +kernel)) ez.rip
  have fa := fz.after_registers readya ea.agrees
    (by simp [xLimbArgumentsEffect, Effect.components, Component.Covers]) (by simp [xLimbArgumentsEffect, Effect.components])
  have ma := ea.agrees.external (by simp [xLimbArgumentsEffect, Effect.components, Component.Covers])
  have source : a.regValue .rdx = stackPtr s-744 :=
    ea.writes.2.2.2.2.1.trans ((ez.agrees.read (n := 64) (r := 12)
      (by simp [xZeroEffect, Effect.components])).trans sourceRegister)
  have output : a.regValue .rdi = stackPtr s-384 :=
    ea.writes.2.1.trans (stack_address fz (by decide))
  have choice : a.regValue .r8 = if decide (x < Operations.domain.p) then 1 else 0 := by
    have h : a.regValue .r8 = ((z.regValue .rax).setWidth 8).setWidth 64 := ea.writes.2.2.2.2.2
    rw [h,vz]
    by_cases hx : x < Operations.domain.p <;> simp [hx]
  have chosen : a.regValue .r15 = if x < Operations.domain.p then 1 else 0 := by
    have h : a.regValue .r15 = ((z.regValue .rax).setWidth 8).setWidth 64 := ea.writes.1
    rw [h,vz]
    by_cases hx : x < Operations.domain.p <;> simp [hx]
  have zeroA := zero.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  have valueA := candidate.of_bytes_eq (t := a) (fun i hi => congrArg (fun m : Ram => m[_]?) ma)
  obtain ⟨nc,u,rc,fu,iu,result,abi,kept,_⟩ := limb_call pre fa (out := 384) (by decide) (by decide)
    0x1095a 0x8861 (by decide) (by decide +kernel) (by decide) ea.rip
    ⟨ea.writes.2.2.1,ea.writes.2.2.2.1⟩ source output zeroA valueA choice
  have result' : MontgomeryAt u (stackPtr s-384) (canonical x) := by
    by_cases hx : x < Operations.domain.p
    · simpa only [BitVec.ofNat_eq_ofNat,hx,decide_true,Bool.true_eq,ite_true,canonical,Nat.mod_eq_of_lt hx] using result
    · simpa only [BitVec.ofNat_eq_ofNat,hx,decide_false,Bool.false_eq_true,ite_false,canonical] using result
  refine ⟨nz+na+nc,u,(rz.trans ra).trans rc,fu,iu,result',
    (abi .r15 (by simp)).trans chosen,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (abi .rbx (by simp)).trans ((ea.agrees.read (n := 64) (r := 3)
        (by simp [xLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 3) (by simp [xZeroEffect,Effect.components])))
    · exact (abi .rbp (by simp)).trans ((ea.agrees.read (n := 64) (r := 5)
        (by simp [xLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 5) (by simp [xZeroEffect,Effect.components])))
    · exact (abi .r12 (by simp)).trans ((ea.agrees.read (n := 64) (r := 12)
        (by simp [xLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 12) (by simp [xZeroEffect,Effect.components])))
    · exact (abi .r13 (by simp)).trans ((ea.agrees.read (n := 64) (r := 13)
        (by simp [xLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 13) (by simp [xZeroEffect,Effect.components])))
    · exact (abi .r14 (by simp)).trans ((ea.agrees.read (n := 64) (r := 14)
        (by simp [xLimbArgumentsEffect,Effect.components])).trans
          (ez.agrees.read (n := 64) (r := 14) (by simp [xZeroEffect,Effect.components])))
  · intro off len hp i hi
    have cases : (off=312 ∧ len=32) ∨ (off=748 ∧ len=1) := by simpa using hp
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [kept 312 32 (by decide) (by decide) (by decide) i hi, ma]
      have h := x_zero_byte ez (off := 448) (len := 32) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have addr : stackPtr t+448#64=stackPtr s-312 := stack_address state (by decide)
      rwa [addr] at h
    · rw [kept 748 1 (by decide) (by decide) (by decide) i hi, ma]
      have h := x_zero_byte ez (off := 12) (len := 1) (by decide) (by
        intro a n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hn
        omega) hi
      have addr : stackPtr t+12#64=stackPtr s-748 := stack_address state (by decide)
      rwa [addr] at h

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
