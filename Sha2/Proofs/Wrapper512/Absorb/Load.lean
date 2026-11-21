import Sha2.Proofs.Common.SHA256.Blocks.Absorb.LoadPair
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Byte
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.CopyCall
import Sha2.Proofs.Wrapper512.Call

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Load
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field


def pointerDisp : Form → Disp
  | .reset _ => .d32 216
  | .finalizeIntoReset _ => .none
  | _ => .d8 16

def lengthDisp : Form → Disp
  | .reset _ => .d32 224
  | .finalizeIntoReset _ => .d8 8
  | _ => .d8 24

def pair (v : Variant) (form : Form) : Sha2.Proofs.Common.SHA256.Absorb.Blocks.Block :=
  .loadPair (BitVec.ofNat 4 (v.traversal form).indexReg)
    (BitVec.ofNat 4 (v.traversal form).dataReg)
    (BitVec.ofNat 4 (v.traversal form).lengthReg) (pointerDisp form) (lengthDisp form)

def tailDisp : Form → Disp
  | .reset _ => .d8 127
  | .finalizeIntoReset _ => .d32 143
  | .traitFinalizeIntoReset _ => .d32 159
  | _ => .d32 367

def tail (v : Variant) (form : Form) : Sha2.Proofs.Common.SHA256.Absorb.Blocks.Block :=
  .loadTail (BitVec.ofNat 4 (v.traversal form).tailReg) (.sib 4 none 0 (tailDisp form))

def tailOffset (v : Variant) (form : Form) : Nat :=
  (v.traversal form).head + match form with
  | .traitFinalizeIntoReset second => if second then 31 else 32
  | _ => (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (pair v form)).length


theorem pair_code {v : Variant} {form : Form} {s : RamState}
    (nondigest : form ≠ .digest) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (v.traversal form).head form) (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (pair v form))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + (v.traversal form).head) (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (pair v form))
  · cases form with
      | slices => cases v <;> decide +kernel +revert
      | digest => cases v <;> simp_all
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> decide +kernel +revert
      | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
      | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
  · cases form with
      | slices => cases v <;> decide +kernel +revert
      | digest => cases v <;> simp_all
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> decide +kernel +revert
      | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
      | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert

theorem tail_code {v : Variant} {form : Form} {s : RamState}
    (nondigest : form ≠ .digest) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (tailOffset v form) form) (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (tail v form))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + tailOffset v form) (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (tail v form))
  · cases form with
      | slices => cases v <;> decide +kernel +revert
      | digest => cases v <;> simp_all
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> decide +kernel +revert
      | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
      | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
  · cases form with
      | slices => cases v <;> decide +kernel +revert
      | digest => cases v <;> simp_all
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> decide +kernel +revert
      | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
      | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert

theorem pair_run [Bindings] {v : Variant} {form : Form}
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    Sha2.Proofs.Common.SHA256.Absorb.Blocks.Contract boundary (v.pc (v.traversal form).head form) (pair v form) := by
  apply Sha2.Proofs.Common.SHA256.Absorb.Blocks.loadPair_run boundary _ _ _ _ _ _ outside
  apply blockInProgram_of_textOffset
  cases form with
  | slices => cases v <;> decide +kernel +revert
  | digest => cases v <;> decide +kernel +revert
  | reset stage =>
    rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
    all_goals cases v <;> decide +kernel +revert
  | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
  | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert

theorem tail_run [Bindings] {v : Variant} {form : Form}
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    Sha2.Proofs.Common.SHA256.Absorb.Blocks.Contract boundary (v.pc (tailOffset v form) form) (tail v form) := by
  apply AdvanceTriple.of_effect
  · intro s ready loaded pre
    exact Sha2.Proofs.Common.SHA256.Absorb.Blocks.loadTail_step _ _ _ pre.valid s ready loaded ⟨pre.rip, pre.readable⟩
  · intro s _
    exact Effect.Avoids.of_noMem (by simp [Sha2.Proofs.Common.SHA256.Absorb.Blocks.effect, tail, Effect.components, Component.Covers]) _
  · intro s hp
    change v.pc (tailOffset v form) form + BitVec.ofNat 64
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (tail v form)).length ≠ boundary.rip
    clear hp s
    apply boundary_ne_program outside
    apply blockInProgram_of_textOffset _ _ _ _ (Nat.le_refl _)
    cases form with
    | slices => cases v <;> decide +kernel +revert
    | digest => cases v <;> decide +kernel +revert
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> decide +kernel +revert
    | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
    | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
end Sha2.Proofs.Wrapper512.Absorb.Load

namespace Sha2.Proofs.Wrapper512.Absorb.Load
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

def cloneSetupBytes (second : Bool) : List UInt8 :=
  [0xba, 0xd0, 0, 0, 0, 0x48, 0x89, 0xdf, 0x4c, 0x89, if second then 0xf6 else 0xe6]

def cloneSetupEffect (p : BitVec 64) (s : RamState) (second : Bool) : Effect :=
  { rip := p + 11
    writes := [⟨(.reg 2 : Operand 64), 208⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rbx⟩,
      ⟨(.reg 6 : Operand 64), s.regValue (if second then .r14 else .r12)⟩] }

theorem clone_setup_code {v : Variant} {second : Bool} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange
      (v.pc ((v.traversal (.traitFinalizeIntoReset second)).head + 18) (.traitFinalizeIntoReset second))
      (cloneSetupBytes second)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset (.traitFinalizeIntoReset second) +
      (v.traversal (.traitFinalizeIntoReset second)).head + 18) (cloneSetupBytes second)
  · cases second <;> cases v <;> decide +kernel
  · cases second <;> cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem clone_setup_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (second : Bool) (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 11) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (cloneSetupBytes second))
      (Effect.post (fun s => cloneSetupEffect p s second)) := by
  cases second
  all_goals
    advance_reloc_begin
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.constant_step p 2 208)
      next (boundary_ne_program outside (inside 5 (by decide)))
    advance_reloc_then
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.move_step (p + 5) 7 3)
      next (by simpa only [BitVec.add_assoc] using boundary_ne_program outside (inside 8 (by decide)))
  ·
    advance_reloc_then
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.move_step (p + 8) 6 12)
      next (by simpa only [BitVec.add_assoc] using boundary_ne_program outside (inside 11 (by decide)))
    advance_finish [cloneSetupEffect, BitVec.add_assoc]
  ·
    advance_reloc_then
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.move_step (p + 8) 6 14)
      next (by simpa only [BitVec.add_assoc] using boundary_ne_program outside (inside 11 (by decide)))
    advance_finish [cloneSetupEffect, BitVec.add_assoc]
end Sha2.Proofs.Wrapper512.Absorb.Load

namespace Sha2.Proofs.Wrapper512.Absorb.Load
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

def cloneCallSite (v : Variant) (second : Bool) : Common.SHA256.Absorb.CallSite :=
  ⟨v.pc ((v.traversal (.traitFinalizeIntoReset second)).head + 29) (.traitFinalizeIntoReset second),
    .register (if second then 5 else 13)⟩

theorem clone_call_code {v : Variant} {second : Bool} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (cloneCallSite v second).pc (cloneCallSite v second).encoding.bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset (.traitFinalizeIntoReset second) +
      (v.traversal (.traitFinalizeIntoReset second)).head + 29) (cloneCallSite v second).encoding.bytes
  · cases second <;> cases v <;> decide +kernel
  · cases second <;> cases v <;> decide +kernel

theorem clone_call [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {second : Bool} (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : State v initial s (.traitFinalizeIntoReset second))
    (rip : s.RIP = (cloneCallSite v second).pc)
    (target : s.regValue (if second then .rbp else .r13) = 0x10dd60) :
    ∃ t, ReturnState v initial t (.traitFinalizeIntoReset second) ∧
      (callEffect (fun _ => 0x10dd60)
        (v.pc (tailOffset v (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second)) s).Holds s t ∧
      stackPtr t = stackPtr initial - 656 ∧
      (returnBoundary t).rip = v.pc (tailOffset v (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) ∧
      Advances (returnBoundary initial) 1 s t := by
  have address : pushAddr s = stackPtr initial - 656 := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    exact Machine.Stages.stack_slot_writable ctx input (by change 656 ≤ 1200; decide) (by decide)
  have separate : RangeApart (pushAddr s) 8 (cloneCallSite v second).pc
      (cloneCallSite v second).encoding.bytes.length := by
    rw [address]
    apply Machine.Stages.stack_slot_codeApart ctx (by change 656 ≤ 1200; decide) (by decide)
    cases second <;> cases v <;> decide +kernel
  have targeted : Common.SHA256.Absorb.CopyCall.Target (cloneCallSite v second) s := by
    cases second <;> exact target
  obtain ⟨t, run, ready, effect⟩ := Common.SHA256.Absorb.CopyCall.enter
    (cloneCallSite v second) (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    (supportedMachine_readyToStep input.machine) (clone_call_code input.loaded)
    ⟨rip, writable, separate⟩ targeted
  have returnedPC : (cloneCallSite v second).pc + BitVec.ofNat 64 (cloneCallSite v second).encoding.bytes.length =
      v.pc (tailOffset v (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) := by
    cases second <;> cases v <;> decide +kernel
  rw [returnedPC] at effect
  obtain ⟨state, rsp, returned⟩ := ReturnState.of_call ctx input run ready effect input.rsp
  exact ⟨t, state, effect, rsp, returned, run⟩
end Sha2.Proofs.Wrapper512.Absorb.Load
