import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.ResetLayout
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Zero

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def startOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x2a6
  | .digest => 0x1c6
  | .reset stage => if stage.val = 2 then
      match v with
      | .sha384 => 0x79b
      | .sha512 => 0x7bb
      | _ => 0x77b
    else 0x454
  | .finalizeIntoReset false => 0x28a
  | .finalizeIntoReset true => match v with
      | .sha384 => 0x601
      | .sha512 => 0x621
      | _ => 0x5e3
  | .traitFinalizeIntoReset false => 0x2f0
  | .traitFinalizeIntoReset true => match v with
      | .sha384 => 0x6c0
      | .sha512 => 0x6e0
      | _ => 0x6a0

def base (last : Bool) (form : Form := .slices) : Nat :=
  form.frameBytes - form.finalMemory.buffer + if last then 56 else 0

def storeBytes (displacement : Nat) : List UInt8 :=
  if displacement = 0 then [0x48,0xc7,0x04,0x24,0,0,0,0]
  else if displacement < 128 then [0x48,0xc7,0x44,0x24,UInt8.ofNat displacement,0,0,0,0]
  else [0x48,0xc7,0x84,0x24,UInt8.ofNat displacement,UInt8.ofNat (displacement / 256),0,0,0,0,0,0]

def bytesAt (base : Nat) : List UInt8 :=
  storeBytes base ++ storeBytes (base+8) ++ storeBytes (base+16) ++
    storeBytes (base+24) ++ storeBytes (base+32) ++ storeBytes (base+40) ++ storeBytes (base+48)

def bytes (last : Bool) (form : Form := .slices) : List UInt8 := bytesAt (base last form)

def offset (last : Bool) (form : Form := .slices) (v : Variant := .sha384) : Nat :=
  startOffset v form + if last then (bytes false form).length else 0

def nextOffset (last : Bool) (form : Form := .slices) (v : Variant := .sha384) : Nat :=
  offset last form v + (bytes last form).length

def pc (offset : Nat) : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 offset

theorem pc_add (offset count : Nat) : pc offset + BitVec.ofNat 64 count = pc (offset+count) := by
  simp only [pc, BitVec.ofNat_add, BitVec.add_assoc]

structure Pre (start base : Nat) (s : RamState) : Prop where
  rip : s.RIP = pc start
  writable : ∀ i ∈ ([0,8,16,24,32,40,48] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 (base+i)) 8
  codeApart : ∀ i ∈ ([0,8,16,24,32,40,48] : List Nat),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + BitVec.ofNat 64 (base+i)) 8 (pc offset) len

def effectAt (start base : Nat) (s : RamState) : Effect :=
  { rip := pc (start + (bytesAt base).length)
    writes := [⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 0)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 8)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 16)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 24)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 32)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 40)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (base + 48)) : Operand 64), 0⟩] }

def effect (v : Variant) (last : Bool) (s : RamState) (form : Form := .slices) : Effect :=
  effectAt (v.textOffset form + offset last form v) (base last form) s

theorem code {v : Variant} {form : Form} (last : Bool) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (offset last form v) form) (bytes last form)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + offset last form v) (bytes last form)
  all_goals cases form with
  | slices | digest => cases v <;> cases last <;> decide +kernel
  | reset stage =>
    have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases hs with rfl | rfl | rfl <;> cases v <;> cases last <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> cases last <;> decide +kernel

set_option hygiene false in
macro "zero_run" pc0:term "," pc1:term "," pc2:term "," pc3:term "," pc4:term "," pc5:term "," pc6:term "," pc7:term "," disp0:term "," disp1:term "," disp2:term "," disp3:term "," disp4:term "," disp5:term "," disp6:term "," d0:term "," d1:term "," d2:term "," d3:term "," d4:term "," d5:term "," d6:term "," len0:term "," len1:term "," len2:term "," len3:term "," len4:term "," len5:term "," len6:term "," c1:term "," c2:term "," c3:term "," c4:term "," c5:term "," c6:term "," bs:term "," total:term : tactic =>
  `(tactic| (
  advance_begin (mov_m64_imm32_effect_step (pc (start + $pc0)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp0) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      exact h.writable $d0 (by simp)
    · x86_norm
      exact h.codeApart $d0 (by simp) (start + $pc0) $len0 (by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart $d0 (by simp) (start + $pc0) $total (by omega)
  case «next» =>
    intro _ _
    change pc (start + $pc0) + BitVec.ofNat 64 $len0 ≠ boundary.rip
    rw [pc_add]
    exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc1) (by omega))
  advance_then (mov_m64_imm32_effect_step (pc (start + $pc1)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp1) (by decide) rfl rfl 0)
  case sub =>
    rw [← pc_add (start + $pc0) $c1]
    exact codeRange_slice_subset (pc (start + $pc0)) $bs $c1 $len1
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable $d1 (by simp)
    · x86_norm
      exact hp.codeApart $d1 (by simp) (start + $pc1) $len1 (by omega)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart $d1 (by simp) (start + $pc0) $total (by omega)
    · change pc (start + $pc1) + BitVec.ofNat 64 $len1 ≠ boundary.rip
      rw [pc_add]
      exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc2) (by omega))
  advance_then (mov_m64_imm32_effect_step (pc (start + $pc2)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp2) (by decide) rfl rfl 0)
  case sub =>
    rw [← pc_add (start + $pc0) $c2]
    exact codeRange_slice_subset (pc (start + $pc0)) $bs $c2 $len2
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable $d2 (by simp)
    · x86_norm
      exact hp.codeApart $d2 (by simp) (start + $pc2) $len2 (by omega)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart $d2 (by simp) (start + $pc0) $total (by omega)
    · change pc (start + $pc2) + BitVec.ofNat 64 $len2 ≠ boundary.rip
      rw [pc_add]
      exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc3) (by omega))
  advance_then (mov_m64_imm32_effect_step (pc (start + $pc3)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp3) (by decide) rfl rfl 0)
  case sub =>
    rw [← pc_add (start + $pc0) $c3]
    exact codeRange_slice_subset (pc (start + $pc0)) $bs $c3 $len3
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable $d3 (by simp)
    · x86_norm
      exact hp.codeApart $d3 (by simp) (start + $pc3) $len3 (by omega)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart $d3 (by simp) (start + $pc0) $total (by omega)
    · change pc (start + $pc3) + BitVec.ofNat 64 $len3 ≠ boundary.rip
      rw [pc_add]
      exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc4) (by omega))
  advance_then (mov_m64_imm32_effect_step (pc (start + $pc4)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp4) (by decide) rfl rfl 0)
  case sub =>
    rw [← pc_add (start + $pc0) $c4]
    exact codeRange_slice_subset (pc (start + $pc0)) $bs $c4 $len4
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable $d4 (by simp)
    · x86_norm
      exact hp.codeApart $d4 (by simp) (start + $pc4) $len4 (by omega)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart $d4 (by simp) (start + $pc0) $total (by omega)
    · change pc (start + $pc4) + BitVec.ofNat 64 $len4 ≠ boundary.rip
      rw [pc_add]
      exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc5) (by omega))
  advance_then (mov_m64_imm32_effect_step (pc (start + $pc5)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp5) (by decide) rfl rfl 0)
  case sub =>
    rw [← pc_add (start + $pc0) $c5]
    exact codeRange_slice_subset (pc (start + $pc0)) $bs $c5 $len5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable $d5 (by simp)
    · x86_norm
      exact hp.codeApart $d5 (by simp) (start + $pc5) $len5 (by omega)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart $d5 (by simp) (start + $pc0) $total (by omega)
    · change pc (start + $pc5) + BitVec.ofNat 64 $len5 ≠ boundary.rip
      rw [pc_add]
      exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc6) (by omega))
  advance_then (mov_m64_imm32_effect_step (pc (start + $pc6)) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 $disp6) (by decide) rfl rfl 0)
  case sub =>
    rw [← pc_add (start + $pc0) $c6]
    exact codeRange_slice_subset (pc (start + $pc0)) $bs $c6 $len6
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable $d6 (by simp)
    · x86_norm
      exact hp.codeApart $d6 (by simp) (start + $pc6) $len6 (by omega)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart $d6 (by simp) (start + $pc0) $total (by omega)
    · change pc (start + $pc6) + BitVec.ofNat 64 $len6 ≠ boundary.rip
      rw [pc_add]
      exact boundary_ne_program outside (inProgram_of_textOffset (start + $pc7) (by omega))
  advance_finish [effectAt, bytesAt, storeBytes, pc_add, Nat.add_assoc]
  ))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base0 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 0) (codeRange (pc start) (bytesAt 0))
      (Effect.post (effectAt start 0)) := by
  zero_run 0, 8, 17, 26, 35, 44, 53, 62, .none, (.d8 8), (.d8 16), (.d8 24), (.d8 32), (.d8 40), (.d8 48), 0, 8, 16, 24, 32, 40, 48, 8, 9, 9, 9, 9, 9, 9, 8, 17, 26, 35, 44, 53, (bytesAt 0), 62

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base16 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 16) (codeRange (pc start) (bytesAt 16))
      (Effect.post (effectAt start 16)) := by
  zero_run 0, 9, 18, 27, 36, 45, 54, 63, (.d8 16), (.d8 24), (.d8 32), (.d8 40), (.d8 48), (.d8 56), (.d8 64), 0, 8, 16, 24, 32, 40, 48, 9, 9, 9, 9, 9, 9, 9, 9, 18, 27, 36, 45, 54, (bytesAt 16), 63

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base32 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 32) (codeRange (pc start) (bytesAt 32))
      (Effect.post (effectAt start 32)) := by
  zero_run 0, 9, 18, 27, 36, 45, 54, 63, (.d8 32), (.d8 40), (.d8 48), (.d8 56), (.d8 64), (.d8 72), (.d8 80), 0, 8, 16, 24, 32, 40, 48, 9, 9, 9, 9, 9, 9, 9, 9, 18, 27, 36, 45, 54, (bytesAt 32), 63

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base56 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 56) (codeRange (pc start) (bytesAt 56))
      (Effect.post (effectAt start 56)) := by
  zero_run 0, 9, 18, 27, 36, 45, 54, 63, (.d8 56), (.d8 64), (.d8 72), (.d8 80), (.d8 88), (.d8 96), (.d8 104), 0, 8, 16, 24, 32, 40, 48, 9, 9, 9, 9, 9, 9, 9, 9, 18, 27, 36, 45, 54, (bytesAt 56), 63

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base72 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 72) (codeRange (pc start) (bytesAt 72))
      (Effect.post (effectAt start 72)) := by
  zero_run 0, 9, 18, 27, 36, 45, 54, 63, (.d8 72), (.d8 80), (.d8 88), (.d8 96), (.d8 104), (.d8 112), (.d8 120), 0, 8, 16, 24, 32, 40, 48, 9, 9, 9, 9, 9, 9, 9, 9, 18, 27, 36, 45, 54, (bytesAt 72), 63

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base88 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 88) (codeRange (pc start) (bytesAt 88))
      (Effect.post (effectAt start 88)) := by
  zero_run 0, 9, 18, 27, 36, 45, 57, 69, (.d8 88), (.d8 96), (.d8 104), (.d8 112), (.d8 120), (.d32 128), (.d32 136), 0, 8, 16, 24, 32, 40, 48, 9, 9, 9, 9, 9, 12, 12, 9, 18, 27, 36, 45, 57, (bytesAt 88), 69

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base240 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 240) (codeRange (pc start) (bytesAt 240))
      (Effect.post (effectAt start 240)) := by
  zero_run 0, 12, 24, 36, 48, 60, 72, 84, (.d32 240), (.d32 248), (.d32 256), (.d32 264), (.d32 272), (.d32 280), (.d32 288), 0, 8, 16, 24, 32, 40, 48, 12, 12, 12, 12, 12, 12, 12, 12, 24, 36, 48, 60, 72, (bytesAt 240), 84

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base256 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 256) (codeRange (pc start) (bytesAt 256))
      (Effect.post (effectAt start 256)) := by
  zero_run 0, 12, 24, 36, 48, 60, 72, 84, (.d32 256), (.d32 264), (.d32 272), (.d32 280), (.d32 288), (.d32 296), (.d32 304), 0, 8, 16, 24, 32, 40, 48, 12, 12, 12, 12, 12, 12, 12, 12, 24, 36, 48, 60, 72, (bytesAt 256), 84

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base296 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 296) (codeRange (pc start) (bytesAt 296))
      (Effect.post (effectAt start 296)) := by
  zero_run 0, 12, 24, 36, 48, 60, 72, 84, (.d32 296), (.d32 304), (.d32 312), (.d32 320), (.d32 328), (.d32 336), (.d32 344), 0, 8, 16, 24, 32, 40, 48, 12, 12, 12, 12, 12, 12, 12, 12, 24, 36, 48, 60, 72, (bytesAt 296), 84

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem run_base312 [Bindings] (start : Nat) (bound : start + 84 < 71757)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre start 312) (codeRange (pc start) (bytesAt 312))
      (Effect.post (effectAt start 312)) := by
  zero_run 0, 12, 24, 36, 48, 60, 72, 84, (.d32 312), (.d32 320), (.d32 328), (.d32 336), (.d32 344), (.d32 352), (.d32 360), 0, 8, 16, 24, 32, 40, 48, 12, 12, 12, 12, 12, 12, 12, 12, 24, 36, 48, 60, 72, (bytesAt 312), 84

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem run [Bindings] {v : Variant} {form : Form} (last : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre (v.textOffset form + offset last form v) (base last form))
      (codeRange (v.pc (offset last form v) form) (bytes last form))
      (Effect.post (fun s => effect v last s form)) := by
  have bound : v.textOffset form + offset last form v + 84 < 71757 := by
    cases form with
    | slices | digest => cases v <;> cases last <;> decide
    | reset stage =>
        have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases hs with rfl | rfl | rfl <;> cases v <;> cases last <;> decide
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v <;> cases last <;> decide
  cases form with
  | slices =>
    cases last
    · exact run_base32 _ bound boundary outside
    · exact run_base88 _ bound boundary outside
  | digest =>
    cases last
    · exact run_base0 _ bound boundary outside
    · exact run_base56 _ bound boundary outside
  | reset _ =>
    cases last
    · exact run_base0 _ bound boundary outside
    · exact run_base56 _ bound boundary outside
  | finalizeIntoReset second =>
    cases second <;> cases last
    · exact run_base16 _ bound boundary outside
    · exact run_base72 _ bound boundary outside
    · exact run_base240 _ bound boundary outside
    · exact run_base296 _ bound boundary outside
  | traitFinalizeIntoReset second =>
    cases second <;> cases last
    · exact run_base256 _ bound boundary outside
    · exact run_base312 _ bound boundary outside
    · exact run_base32 _ bound boundary outside
    · exact run_base88 _ bound boundary outside

end Sha2.Proofs.Wrapper512.Hash.Finalize.Zero
