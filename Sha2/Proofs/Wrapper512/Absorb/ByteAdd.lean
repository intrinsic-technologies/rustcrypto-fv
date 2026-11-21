import Sha2.Proofs.Wrapper512.Absorb.Copy
import Sha2.Proofs.Wrapper.Absorb.ByteAdd
import Sha2.Proofs.Wrapper512.Dispatch.Run
import Sha2.Proofs.Common.Instructions.AddByte.Effect

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions.AddByte X86.Helpers

def shortAddOffset (v : Variant) (form : Form := .slices) : Nat :=
  Copy.Site.short.relativeOffset form v + Copy.Site.short.size v form

def shortLengthRegister (v : Variant) (form : Form) : BitVec 5 :=
  BitVec.ofNat 5 (v.traversal form).lengthReg

def shortPositionRegister (v : Variant) (form : Form) : BitVec 5 :=
  BitVec.ofNat 5 (v.traversal form).tailReg

def shortAddRex (v : Variant) (form : Form) : UInt8 :=
  UInt8.ofNat (64 + (shortLengthRegister v form).toNat / 8 +
    4 * ((shortPositionRegister v form).toNat / 8))

def shortAddModrm (v : Variant) (form : Form) : UInt8 :=
  UInt8.ofNat (192 + (shortLengthRegister v form).toNat % 8 +
    8 * ((shortPositionRegister v form).toNat % 8))

theorem short_add_step [Bindings] (v : Variant) (form : Form) :
    StepEffect (fun s => s.RIP = v.pc (shortAddOffset v form) form)
      (codeRange (v.pc (shortAddOffset v form) form)
        [shortAddRex v form, 0x00, shortAddModrm v form])
      (addR8R8Effect (v.pc (shortAddOffset v form) form)
        (shortLengthRegister v form) (shortPositionRegister v form)) := by
  have rex : RexPrefix (shortAddRex v form).toBitVec := by
    unfold RexPrefix
    cases v <;> cases form with
    | reset stage => revert stage; decide +kernel
    | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
    | _ => decide +kernel
  have modrm : modrmMod (shortAddModrm v form) = 3 := by
    clear rex
    cases v <;> cases form with
    | reset stage => revert stage; decide +kernel
    | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
    | _ => decide +kernel
  have regs :
      gprNumber 0 (rexB (shortAddRex v form).toBitVec) (modrmRm (shortAddModrm v form)) =
        shortLengthRegister v form ∧
      gprNumber 0 (rexR (shortAddRex v form).toBitVec) (modrmReg (shortAddModrm v form)) =
        shortPositionRegister v form := by
    clear rex modrm
    cases v <;> cases form with
    | reset stage => revert stage; decide +kernel
    | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
    | _ => decide +kernel
  simpa only [regs.1, regs.2] using add_r8_r8_effect_step
    (v.pc (shortAddOffset v form) form) (shortAddRex v form) (shortAddModrm v form) rex modrm

theorem short_add_bytes (v : Variant) (form : Form) (hd : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + shortAddOffset v form) 3 =
      [shortAddRex v form, 0x00, shortAddModrm v form] := by
  cases v <;> cases form with
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel

theorem short_add_register_safe (v : Variant) (form : Form) :
    shortLengthRegister v form ≠ 4 ∧
    (form = .traitFinalizeIntoReset false → shortLengthRegister v form ≠
      (if v = .sha512 then 13 else 5)) := by
  cases v <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem short_add_bound (v : Variant) (form : Form) :
    v.textOffset form + shortAddOffset v form + 3 < 71757 := by
  cases v <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem add_short_length_local [Bindings] {v : Variant} {form : Form}
    {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (rip : s.RIP = v.pc (shortAddOffset v form) form)
    (hd : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧
      t.RIP = v.pc (shortAddOffset v form + 3) form ∧
      (Operand.reg (shortLengthRegister v form) : Operand 8).read t =
        (Operand.reg (shortLengthRegister v form) : Operand 8).read s +
        (Operand.reg (shortPositionRegister v form) : Operand 8).read s ∧
      AgreesExcept [.reg (shortLengthRegister v form), .flags, .rip] s t ∧
      Advances (returnBoundary initial) 1 s t := by
  obtain ⟨t, run, ready, effect⟩ := (short_add_step v form).advances (boundary := returnBoundary initial)
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded)
      (v.textOffset form + shortAddOffset v form)
      [shortAddRex v form, 0x00, shortAddModrm v form]
      (Nat.le_of_lt (short_add_bound v form)) (short_add_bytes v form hd)) rip
    (by
      change v.pc (shortAddOffset v form) form + BitVec.ofNat 64 3 ≠ _
      rw [Variant.pc_add v (shortAddOffset v form) 3 form]
      exact boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
        (inProgram_of_textOffset (v.textOffset form + (shortAddOffset v form + 3))
          (by have := short_add_bound v form; omega)))
  have frame : AgreesExcept [.reg (shortLengthRegister v form), .flags, .rip] s t := effect.agrees
  refine ⟨t, preserved_of_agrees ctx input run ready frame ?_ ?_
    (by simp) (fun h => (hd h).elim) ?_,
    effect.rip.trans (Variant.pc_add v (shortAddOffset v form) 3 form), ?_, frame, run⟩
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ha.elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
      reduceCtorEq, or_false]
    exact Ne.symm (short_add_register_safe v form).1
  · intro hf
    left
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
      reduceCtorEq, or_false]
    exact Ne.symm ((short_add_register_safe v form).2 hf)
  · have write : (Operand.reg (shortLengthRegister v form) : Operand 64).read t = mergeGPR 8
        ((Operand.reg (shortLengthRegister v form) : Operand 8).read s +
          (Operand.reg (shortPositionRegister v form) : Operand 8).read s)
        ((Operand.reg (shortLengthRegister v form) : Operand 64).read s) := effect.writes
    have low : (Operand.reg (shortLengthRegister v form) : Operand 8).read t =
        ((Operand.reg (shortLengthRegister v form) : Operand 64).read t).setWidth 8 := rfl
    rw [low, write, Wrapper.Absorb.mergeGPR8_low]

theorem add_short_length [Bindings] {v : Variant} {form : Form}
    {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (rip : s.RIP = v.pc (shortAddOffset v form) form)
    (hd : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧
      t.RIP = v.pc (shortAddOffset v form + 3) form ∧
      (Operand.reg (shortLengthRegister v form) : Operand 8).read t =
        (Operand.reg (shortLengthRegister v form) : Operand 8).read s +
        (Operand.reg (shortPositionRegister v form) : Operand 8).read s ∧
      AgreesExcept [.reg (shortLengthRegister v form), .flags, .rip] s t := by
  obtain ⟨t, preserved, rip, value, frame, _⟩ := add_short_length_local ctx input rip hd
  exact ⟨t, preserved, rip, value, frame⟩

end Sha2.Proofs.Wrapper512.Absorb
