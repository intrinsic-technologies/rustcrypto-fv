import P256.Proofs.Sec1.Decompress.Input.FirstSelect
import P256.Proofs.Sec1.Decompress.Input.CopyMemory
import P256.Proofs.Sec1.Decompress.Input.SelectSetup
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.Sec1.Decompress.Cubic (montgomeryAt_of_copy)

def selectSite : FieldCall.BinaryCallSite 2592 408 0x114380 128 := {
  codeOffset := 0xfdc7
  disp := 0x45b4
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨416,184,288,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 152
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide }

theorem finish [Bindings] {s v : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} {x : Nat} (pre : Pre s boundary bytes odd)
    (state : LimbState s v x odd) :
    ∃ fuel t, Advances boundary fuel v t ∧ InputState s t x odd := by
  obtain ⟨nc,w,rc,readyc,_,ec⟩ := copy_correct boundary pre.outerBoundary v
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfd41 copyBytes (by decide +kernel) (by decide +kernel))
    (copy_pre pre.toCalleePre state.toFrameState state.rip)
  have framec := copy_frame pre.toCalleePre state.toFrameState readyc ec
  have candc := copy_value pre.toCalleePre state.toFrameState ec (x := checkedX x) (by
    have address : stackPtr v + 80 = stackPtr s - 328 := Cubic.input_stack_address state.rsp (offset := 80) (by decide)
    rw [address]
    exact state.value)
  have candAddr : stackPtr v+256=stackPtr s-152 := Cubic.input_stack_address state.rsp (offset := 256) (by decide)
  rw [candAddr] at candc
  have signc : (Operand.mem (stackPtr s-332) : Operand 32).read w = BitVec.ofNat 32 odd.toNat := by
    have h := copy_read ec (off := 76) (n := 32) (by decide) (.inl (by decide))
    have ha : stackPtr v+76=stackPtr s-332 := Cubic.input_stack_address state.rsp (offset := 76) (by decide)
    change (Operand.mem (stackPtr v+76) : Operand 32).read w = (Operand.mem (stackPtr v+76) : Operand 32).read v at h
    rw [ha] at h
    exact h.trans state.parity
  have outc : (Operand.mem (stackPtr s-224) : Operand 64).read w = s.regValue .rdi := by
    have h := copy_read ec (off := 184) (n := 64) (by decide) (.inl (by decide))
    have ha : stackPtr v+184=stackPtr s-224 := Cubic.input_stack_address state.rsp (offset := 184) (by decide)
    change (Operand.mem (stackPtr v+184) : Operand 64).read w = (Operand.mem (stackPtr v+184) : Operand 64).read v at h
    rw [ha] at h
    exact h.trans state.output
  obtain ⟨nz,z,rz,readyz,_,ez⟩ := final_zero_correct boundary pre.outerBoundary w readyc
    (programText_slice (programLoaded_codeIn framec.loaded) 0xfd75 finalZeroBytes (by decide +kernel) (by decide +kernel))
    (finalZero_pre pre.toCalleePre framec ec.rip)
  have framez := finalZero_frame pre.toCalleePre framec readyz ez
  have zeroz := finalZero_value pre.toCalleePre framec ez
  have zeroAddr : stackPtr w+224=stackPtr s-184 := Cubic.input_stack_address framec.rsp (offset := 224) (by decide)
  rw [zeroAddr] at zeroz
  have candz : MontgomeryAt z (stackPtr s-152) (checkedX x) := by
    apply montgomeryAt_of_copy candc
    intro i hi
    have h := finalZero_byte ez (off := 256) (len := 32) (by decide) (.inl (by decide)) (.inr (by decide)) hi
    have ha : stackPtr w+256=stackPtr s-152 := Cubic.input_stack_address framec.rsp (offset := 256) (by decide)
    change z.external[stackPtr w+256+BitVec.ofNat 64 i]? = w.external[stackPtr w+256+BitVec.ofNat 64 i]? at h
    rwa [ha] at h
  have signz : (Operand.mem (stackPtr s-332) : Operand 32).read z = BitVec.ofNat 32 odd.toNat := by
    have h := finalZero_read ez (off := 76) (n := 32) (by decide) (.inl (by decide)) (.inl (by decide))
    have ha : stackPtr w+76=stackPtr s-332 := Cubic.input_stack_address framec.rsp (offset := 76) (by decide)
    change (Operand.mem (stackPtr w+76) : Operand 32).read z = (Operand.mem (stackPtr w+76) : Operand 32).read w at h
    rw [ha] at h
    exact h.trans signc
  have outz : (Operand.mem (stackPtr s-224) : Operand 64).read z = s.regValue .rdi := by
    have h := finalZero_read ez (off := 184) (n := 64) (by decide) (.inl (by decide)) (.inl (by decide))
    have ha : stackPtr w+184=stackPtr s-224 := Cubic.input_stack_address framec.rsp (offset := 184) (by decide)
    change (Operand.mem (stackPtr w+184) : Operand 64).read z = (Operand.mem (stackPtr w+184) : Operand 64).read w at h
    rw [ha] at h
    exact h.trans outc
  have validz : z.regValue .rbp = if x < P256.Spec.Operations.domain.p then 1 else 0 :=
    ((ez.agrees.read (n := 64) (r := 5) (by simp [finalZeroEffect, Effect.components])).trans
      (ec.agrees.read (n := 64) (r := 5) (by simp [copyEffect, Effect.components]))).trans state.valid
  obtain ⟨np,p,rp,readyp,_,ep⟩ := selectSetup_correct boundary pre.outerBoundary z readyz
    (programText_slice (programLoaded_codeIn framez.loaded) 0xfdad selectSetupBytes (by decide +kernel) (by decide +kernel)) ez.rip
  have framep := framez.after_registers readyp ep.agrees
    (by simp [selectSetupEffect, Effect.components, Component.Covers]) (by simp [selectSetupEffect, Effect.components])
  have memp := ep.agrees.external (by simp [selectSetupEffect, Effect.components, Component.Covers])
  have source : p.regValue .rsi = stackPtr s - 184 :=
    ep.writes.2.1.trans (Cubic.input_stack_address framez.rsp (offset := 224) (by decide))
  have right : p.regValue .rdx = stackPtr s - 152 :=
    ep.writes.2.2.1.trans (Cubic.input_stack_address framez.rsp (offset := 256) (by decide))
  have output : p.regValue .rdi = stackPtr s - 288 :=
    ep.writes.2.2.2.1.trans (Cubic.input_stack_address framez.rsp (offset := 120) (by decide))
  have base : p.regValue .r15 = stackPtr s - 288 :=
    ep.writes.1.trans (Cubic.input_stack_address framez.rsp (offset := 120) (by decide))
  have chosen : p.regValue .rcx = if decide (x < P256.Spec.Operations.domain.p) then 1 else 0 := by
    have h : p.regValue .rcx = ((z.regValue .rbp).setWidth 32).setWidth 64 := ep.writes.2.2.2.2
    rw [h, validz]
    by_cases hx : x < P256.Spec.Operations.domain.p <;> simp [hx]
  have zeroP : MontgomeryAt p (stackPtr s - 184) 0 := zeroz.of_bytes_eq
    (fun i hi => congrArg (fun m : Ram => m[_]?) memp)
  have candP : MontgomeryAt p (stackPtr s - 152) (checkedX x) := candz.of_bytes_eq
    (fun i hi => congrArg (fun m : Ram => m[_]?) memp)
  obtain ⟨n, t, run, frame, rip, value, abi, kept, _⟩ :=
    PublicPoint.Normalize.select_binary_call
      (op := fun _ y => if decide (x < P256.Spec.Operations.domain.p) then y else 0)
      pre.toCalleePre framep selectSite
      (fun entry hp choice left right =>
        Projective.Multiply.Machine.Lookup.Select.field_select_correct hp left right (choice.trans chosen))
      ep.rip source right output zeroP candP
  have keep (off n : Nat) (ho : off ≤ 408) (hl : n/8 ≤ off+8)
      (apart : off+32 ≤ 288 ∨ 288+n/8 ≤ off) :
      memLoad t.external (stackPtr s-BitVec.ofNat 64 off) n =
        memLoad z.external (stackPtr s-BitVec.ofNat 64 off) n := by
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = _
    rw [kept off (n/8) ho hl apart i hi, memp]
    rfl
  change MontgomeryAt t (stackPtr s - 288)
    (if decide (x < P256.Spec.Operations.domain.p) then checkedX x else 0) at value
  have value' : MontgomeryAt t (stackPtr s - 288) (checkedX x) := by
    by_cases hx : x < P256.Spec.Operations.domain.p
    · simpa only [hx, decide_true, Bool.true_eq, ite_true] using value
    · simpa only [checkedX, hx, decide_false, Bool.false_eq_true, ite_false] using value
  refine ⟨nc+nz+np+n, t, ((rc.trans rz).trans rp).trans run,
    ⟨⟨frame, ?_, ?_, ?_, value'⟩, rip, ?_, (abi .r15 (by simp)).trans base⟩⟩
  · exact (keep 224 64 (by decide) (by decide) (.inl (by decide))).trans outz
  · exact (keep 332 32 (by decide) (by decide) (.inr (by decide))).trans signz
  · have h : t.regValue .rbp = if x < P256.Spec.Operations.domain.p then 1 else 0 :=
      (abi .rbp (by simp)).trans ((ep.agrees.read (n := 64) (r := 5)
        (by simp [selectSetupEffect, Effect.components])).trans validz)
    rw [h]
    by_cases hx : x < P256.Spec.Operations.domain.p <;> simp [hx]
  · exact (abi .r14 (by simp)).trans
      ((ep.agrees.read (n := 64) (r := 14) (by simp [selectSetupEffect, Effect.components])).trans
        ((ez.agrees.read (n := 64) (r := 14) (by simp [finalZeroEffect, Effect.components])).trans
          ((ec.agrees.read (n := 64) (r := 14) (by simp [copyEffect, Effect.components])).trans state.r14)))

end P256.Proofs.Sec1.Decompress.Input
