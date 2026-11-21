import Sha2.Proofs.Wrapper512.Dispatch.Store
import Sha2.Proofs.Common.Field.Operations.Run.Compose
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

namespace Sha2.Proofs.Wrapper512.Dispatch.Store

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] byteStore_local

def suffixBytes (v : Variant) (form : Form) : List UInt8 :=
  (bytes v form).drop (suffixOffset form v - startOffset form v)

theorem bytes_length (v : Variant) (form : Form := .slices) :
    (bytes v form).length = (match form with | .slices => 191 | _ => suffixLength form) := by
  cases form <;> cases v <;> dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister] <;> decide +kernel +revert

theorem suffixBytes_length (v : Variant) (form : Form) :
    (suffixBytes v form).length = suffixLength form := by
  cases form <;> cases v <;> dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister] <;> decide +kernel +revert

def registerWrites (v : Variant) (form : Form) : List Write :=
  match form with
  | .reset _ => (List.range 8).map (fun i =>
      ⟨(.reg (BitVec.ofNat 5 (wordRegister v form i)) : Operand 64), v.initialHash[i]!.toBitVec⟩)
  | _ => [⟨(.reg 0 : Operand 64), v.initialHash[0]!.toBitVec⟩]

def effectWithRegister (v : Variant) (s : RamState) (form : Form := .slices) : Effect :=
  { (effect v s form) with
    writes := (effect v s form).writes ++ registerWrites v form }

def suffixWithRegister (v : Variant) (s : RamState) (form : Form) : Effect :=
  { (suffixEffect v s form) with
    writes := (suffixEffect v s form).writes ++ registerWrites v form }

theorem slot_mem (form : Form) (offset width : Nat)
    (member : (offset, width) ∈ [(0x170,8),(0x178,8),(0x180,8),(0x188,8),(0x190,8),(0x198,8),(0x1a0,8),(0x1a8,8),(0x1b0,8),(0x1b8,8),(0x16f,1)]) :
    (slotOffset form offset, width) ∈ slots form :=
  List.mem_append_right _ (List.mem_map.mpr ⟨(offset,width), member, rfl⟩)

theorem slot_signed (form : Form) (n : Nat)
    (hn : n ∈ [367,368,376,384,392,400,408,416,424,432,440]) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (slotOffset form n)) =
      BitVec.ofNat 64 (slotOffset form n) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  cases form <;>
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def shiftedBase (base : BitVec 64) : Form → BitVec 64
  | .slices => base
  | .digest => base - 32
  | .reset _ => base - 240
  | .finalizeIntoReset _ => base - 224
  | .traitFinalizeIntoReset _ => base + 16

theorem slot_address (base : BitVec 64) (form : Form) (n : Nat)
    (hn : n ∈ [367,368,376,384,392,400,408,416,424,432,440]) :
    base + BitVec.ofNat 64 (slotOffset form n) = shiftedBase base form + BitVec.ofNat 64 n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  cases form <;> rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [slotOffset, shiftedBase]
  all_goals simp only [Nat.reduceSub, Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]

theorem tail_value (form : Form) : (tailDisp form).value = BitVec.ofNat 64 (slotOffset form 367) := by
  cases form <;> rfl

theorem tail_size (form : Form) : (tailDisp form).bytes.length + 172 = suffixLength form := by
  cases form <;> rfl

theorem wordRegister_values (v : Variant) (form : Form) (word : Nat) :
    wordRegister v form word = 0 ∨ wordRegister v form word = 1 ∨
    wordRegister v form word = 2 ∨ wordRegister v form word = 6 ∨
    wordRegister v form word = 7 ∨ wordRegister v form word = 8 ∨
    wordRegister v form word = 9 ∨ wordRegister v form word = 10 ∨
    wordRegister v form word = 11 := by
  by_cases bound : word < 8
  · have h : word = 0 ∨ word = 1 ∨ word = 2 ∨ word = 3 ∨ word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases form <;> cases v <;> dsimp only [wordRegister] <;> decide +kernel +revert
  · cases form <;> cases v <;> dsimp only [wordRegister]
    all_goals simp [getElem!_neg, bound]

theorem immediateRegister_eq (v : Variant) (form : Form) (word : Nat) :
    gprNumber (0#1) (rexB (immediateRex v form word).toBitVec) (opcodeReg (immediateOpcode v form word)) = BitVec.ofNat 5 (wordRegister v form word) := by
  dsimp only [immediateRex, immediateOpcode]
  have h := wordRegister_values v form word
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals rw [h] <;> decide +kernel

theorem storeRegister_eq (v : Variant) (form : Form) (word : Nat) :
    gprNumber (0#1) (rexR (storeRex v form word).toBitVec) (storeRegister v form word) = BitVec.ofNat 5 (wordRegister v form word) := by
  dsimp only [storeRex, storeRegister]
  have h := wordRegister_values v form word
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals rw [h] <;> decide +kernel

theorem wordRegister_ne_rsp (v : Variant) (form : Form) (word : Nat) :
    BitVec.ofNat 5 (wordRegister v form word) ≠ (4#5) := by
  have h := wordRegister_values v form word
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals rw [h] <;> decide +kernel

theorem rsp_ne_wordRegister (v : Variant) (form : Form) (word : Nat) :
    (4#5) ≠ BitVec.ofNat 5 (wordRegister v form word) := by
  have h := wordRegister_values v form word
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals rw [h] <;> decide +kernel

theorem wordRegister_eq_iff (v : Variant) (form : Form) (i j : Nat)
    (hi : i < 8) (hj : j < 8) :
    (BitVec.ofNat 5 (wordRegister v form i) = BitVec.ofNat 5 (wordRegister v form j)) ↔
      (match form with | .reset _ => i = j | _ => True) := by
  have ei : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  have ej : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases ei with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases ej with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases form <;> cases v <;> dsimp only [wordRegister] <;> decide +kernel +revert

theorem wordRegister_rax (v : Variant) (form : Form) (word : Nat)
    (h : match form with | .reset _ => False | _ => True) :
    wordRegister v form word = 0 := by
  cases form <;> first | exact h.elim | rfl

attribute [local x86_compose] wordRegister_rax shiftedBase BitVec.sub_eq_add_neg BitVec.add_assoc

attribute [local x86_compose] slot_signed slot_address tail_value wordRegister_eq_iff tailDisp suffixLength immediateRegister_eq storeRegister_eq wordRegister_ne_rsp rsp_ne_wordRegister

macro "sha512_init_begin " step:term : tactic => `(tactic| (
  refine Sha2.Proofs.Common.Field.AdvanceTriple.block_first ?k $step ?sub ?pre ?av ?«next»
  case pre => intro s hP; exact hP.rip
  case av => intro _ _; x86_avoid
  case' k => x86_norm))

macro "sha512_init_then " step:term : tactic => `(tactic| (
  refine Sha2.Proofs.Common.Field.AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid
  case loc => x86_local
  case full => x86_full
  case' k => x86_norm))

set_option maxHeartbeats 1000000 in
macro "sha512_initialize_suffix_for " variant:term "," _ret:term "," out:term "," shape:term : tactic =>
  `(tactic| (
      have lengthBound : 173 ≤ suffixLength $shape := by (try dsimp only [suffixLength]) <;> decide
      have programBound : ($variant).textOffset $shape + suffixOffset $shape $variant + (suffixLength $shape) ≤ 71757 := by
        cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide
      sha512_init_begin (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 0) $shape) (immediateRex $variant $shape 7) (immediateOpcode $variant $shape 7) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[7]!.toBitVec)
      case sub =>
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 0 10
        have hbytes : (immediateRex $variant $shape 7 :: immediateOpcode $variant $shape 7 :: immBytes 64 (($variant).initialHash[7]!.toBitVec)) = ((suffixBytes $variant $shape).drop 0).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        simpa only [BitVec.add_zero, Nat.add_zero] using hslice
      case «next» =>
        intro s h
        exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 10 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 10) $shape) (storeRex $variant $shape 7) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 7) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 424)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 10 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 10 8
        have hbytes : (storeRex $variant $shape 7 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 424)))).modrm (storeRegister $variant $shape 7) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 424)))).tail) = ((suffixBytes $variant $shape).drop 10).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 0) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 10) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 0) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 424,8) (slot_mem $shape 424 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 424,8) (slot_mem $shape 424 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 10)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 424,8) (slot_mem $shape 424 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 18 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 18) $shape) (immediateRex $variant $shape 6) (immediateOpcode $variant $shape 6) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[6]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 18 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 18 10
        have hbytes : (immediateRex $variant $shape 6 :: immediateOpcode $variant $shape 6 :: immBytes 64 (($variant).initialHash[6]!.toBitVec)) = ((suffixBytes $variant $shape).drop 18).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 10) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 28 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 28) $shape) (storeRex $variant $shape 6) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 6) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 416)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 28 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 28 8
        have hbytes : (storeRex $variant $shape 6 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 416)))).modrm (storeRegister $variant $shape 6) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 416)))).tail) = ((suffixBytes $variant $shape).drop 28).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 18) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 28) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 18) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 416,8) (slot_mem $shape 416 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 416,8) (slot_mem $shape 416 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 28)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 416,8) (slot_mem $shape 416 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 36 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 36) $shape) (immediateRex $variant $shape 5) (immediateOpcode $variant $shape 5) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[5]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 36 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 36 10
        have hbytes : (immediateRex $variant $shape 5 :: immediateOpcode $variant $shape 5 :: immBytes 64 (($variant).initialHash[5]!.toBitVec)) = ((suffixBytes $variant $shape).drop 36).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 28) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 46 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 46) $shape) (storeRex $variant $shape 5) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 5) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 408)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 46 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 46 8
        have hbytes : (storeRex $variant $shape 5 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 408)))).modrm (storeRegister $variant $shape 5) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 408)))).tail) = ((suffixBytes $variant $shape).drop 46).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 36) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 46) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 36) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 408,8) (slot_mem $shape 408 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 408,8) (slot_mem $shape 408 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 46)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 408,8) (slot_mem $shape 408 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 54 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 54) $shape) (immediateRex $variant $shape 4) (immediateOpcode $variant $shape 4) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[4]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 54 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 54 10
        have hbytes : (immediateRex $variant $shape 4 :: immediateOpcode $variant $shape 4 :: immBytes 64 (($variant).initialHash[4]!.toBitVec)) = ((suffixBytes $variant $shape).drop 54).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 46) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 64 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 64) $shape) (storeRex $variant $shape 4) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 4) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 400)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 64 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 64 8
        have hbytes : (storeRex $variant $shape 4 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 400)))).modrm (storeRegister $variant $shape 4) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 400)))).tail) = ((suffixBytes $variant $shape).drop 64).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 54) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 64) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 54) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 400,8) (slot_mem $shape 400 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 400,8) (slot_mem $shape 400 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 64)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 400,8) (slot_mem $shape 400 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 72 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 72) $shape) (immediateRex $variant $shape 3) (immediateOpcode $variant $shape 3) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[3]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 72 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 72 10
        have hbytes : (immediateRex $variant $shape 3 :: immediateOpcode $variant $shape 3 :: immBytes 64 (($variant).initialHash[3]!.toBitVec)) = ((suffixBytes $variant $shape).drop 72).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 64) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 82 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 82) $shape) (storeRex $variant $shape 3) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 3) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 392)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 82 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 82 8
        have hbytes : (storeRex $variant $shape 3 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 392)))).modrm (storeRegister $variant $shape 3) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 392)))).tail) = ((suffixBytes $variant $shape).drop 82).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 72) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 82) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 72) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 392,8) (slot_mem $shape 392 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 392,8) (slot_mem $shape 392 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 82)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 392,8) (slot_mem $shape 392 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 90 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 90) $shape) (immediateRex $variant $shape 2) (immediateOpcode $variant $shape 2) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[2]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 90 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 90 10
        have hbytes : (immediateRex $variant $shape 2 :: immediateOpcode $variant $shape 2 :: immBytes 64 (($variant).initialHash[2]!.toBitVec)) = ((suffixBytes $variant $shape).drop 90).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 82) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 100 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 100) $shape) (storeRex $variant $shape 2) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 2) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 384)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 100 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 100 8
        have hbytes : (storeRex $variant $shape 2 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 384)))).modrm (storeRegister $variant $shape 2) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 384)))).tail) = ((suffixBytes $variant $shape).drop 100).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 90) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 100) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 90) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 384,8) (slot_mem $shape 384 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 384,8) (slot_mem $shape 384 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 100)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 384,8) (slot_mem $shape 384 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 108 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 108) $shape) (immediateRex $variant $shape 1) (immediateOpcode $variant $shape 1) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[1]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 108 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 108 10
        have hbytes : (immediateRex $variant $shape 1 :: immediateOpcode $variant $shape 1 :: immBytes 64 (($variant).initialHash[1]!.toBitVec)) = ((suffixBytes $variant $shape).drop 108).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 100) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 118 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 118) $shape) (storeRex $variant $shape 1) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 1) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 376)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 118 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 118 8
        have hbytes : (storeRex $variant $shape 1 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 376)))).modrm (storeRegister $variant $shape 1) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 376)))).tail) = ((suffixBytes $variant $shape).drop 118).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 108) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 118) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 108) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 376,8) (slot_mem $shape 376 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 376,8) (slot_mem $shape 376 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 118)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 376,8) (slot_mem $shape 376 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 126 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_r64_imm64_effect_step (($variant).pc (suffixOffset $shape $variant + 126) $shape) (immediateRex $variant $shape 0) (immediateOpcode $variant $shape 0) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [MovImmOpcode] <;> decide +kernel +revert) ($variant).initialHash[0]!.toBitVec)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 126 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 126 10
        have hbytes : (immediateRex $variant $shape 0 :: immediateOpcode $variant $shape 0 :: immBytes 64 (($variant).initialHash[0]!.toBitVec)) = ((suffixBytes $variant $shape).drop 126).take 10 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨(by apply hH.rip_of; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 118) 8 $shape), Effect.Avoids.of_noMem ?_ _, ?_⟩
        · simp [Component.Covers]
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 136 < 1024) $shape; simpa [movR64Imm64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_r64_effect_step (($variant).pc (suffixOffset $shape $variant + 136) $shape) (storeRex $variant $shape 0) (by cases ($variant) <;> (try dsimp only [immediateRex, immediateOpcode, storeRex, wordRegister]) <;> simp only [RexWPrefix] <;> decide +kernel +revert) (storeRegister $variant $shape 0) (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 368)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexB]) <;> decide +kernel +revert) (by cases ($variant) <;> (try dsimp only [storeRex, wordRegister, AddrMode.rexX]) <;> decide +kernel +revert))
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 136 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 136 8
        have hbytes : (storeRex $variant $shape 0 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 368)))).modrm (storeRegister $variant $shape 0) :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 368)))).tail) = ((suffixBytes $variant $shape).drop 136).take 8 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 126) $shape + 10#64 = ($variant).pc (suffixOffset $shape $variant + 136) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 126) 10 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 368,8) (slot_mem $shape 368 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 368,8) (slot_mem $shape 368 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 136)) 8 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 368,8) (slot_mem $shape 368 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 144 < 1024) $shape; simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_imm32_effect_step (($variant).pc (suffixOffset $shape $variant + 144) $shape) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 440)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) rfl rfl 0)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 144 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 144 12
        have hbytes : (0x48 :: 0xc7 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 440)))).modrm 0 :: ((AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 440)))).tail ++ immBytes 32 0)) = ((suffixBytes $variant $shape).drop 144).take 12 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 136) $shape + 8#64 = ($variant).pc (suffixOffset $shape $variant + 144) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 136) 8 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 440,8) (slot_mem $shape 440 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 440,8) (slot_mem $shape 440 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 144)) 12 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 440,8) (slot_mem $shape 440 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 156 < 1024) $shape; simpa [movM64Imm32Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m64_imm32_effect_step (($variant).pc (suffixOffset $shape $variant + 156) $shape) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 432)))) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) rfl rfl 0)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 156 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 156 12
        have hbytes : (0x48 :: 0xc7 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 432)))).modrm 0 :: ((AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (slotOffset $shape 432)))).tail ++ immBytes 32 0)) = ((suffixBytes $variant $shape).drop 156).take 12 := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 144) $shape + 12#64 = ($variant).pc (suffixOffset $shape $variant + 156) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 144) 12 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 432,8) (slot_mem $shape 432 8 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 432,8) (slot_mem $shape 432 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 156)) 12 (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 432,8) (slot_mem $shape 432 8 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + 168 < 1024) $shape; simpa [movM64Imm32Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      sha512_init_then (mov_m8_imm8_effect_step (($variant).pc (suffixOffset $shape $variant + 168) $shape) (.sib 4 none 0 (tailDisp $shape)) (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide +kernel +revert) rfl rfl 0)
      case sub =>
        rw [← Variant.pc_add $variant (suffixOffset $shape $variant) 168 $shape]
        have hslice := codeRange_slice_subset (($variant).pc (suffixOffset $shape $variant) $shape) (suffixBytes $variant $shape) 168 (suffixLength $shape - 168)
        have hbytes : (0xc6 :: (AddrMode.sib 4 none 0 (tailDisp $shape)).modrm 0 :: ((AddrMode.sib 4 none 0 (tailDisp $shape)).tail ++ immBytes 8 0)) = ((suffixBytes $variant $shape).drop 168).take (suffixLength $shape - 168) := by cases ($variant) <;> (try dsimp only [suffixBytes, bytes, suffixOffset, startOffset, slotOffset, Variant.pc, Variant.textOffset, suffixLength, tailDisp, immediateRex, immediateOpcode, storeRex, storeRegister, wordRegister]) <;> decide +kernel +revert
        rw [hbytes]
        exact hslice
      case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by change ($variant).pc (suffixOffset $shape $variant + 156) $shape + 12#64 = ($variant).pc (suffixOffset $shape $variant + 168) $shape; simpa only [Nat.add_assoc] using Variant.pc_add $variant (suffixOffset $shape $variant + 156) 12 $shape) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_address, rspOf, Operand.read, gprIndex] using hP.writable (slotOffset $shape 367,1) (slot_mem $shape 367 1 (by decide))
        · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [suffixLength, wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 367,1) (slot_mem $shape 367 1 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant + 168)) (suffixLength $shape - 168) (by omega)
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister]
          simpa [suffixLength, wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, shiftedBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, slot_signed, slot_address, suffixBytes_length, Variant.pc, Nat.add_assoc, rspOf, Operand.read, gprIndex] using hP.codeApart (slotOffset $shape 367,1) (slot_mem $shape 367 1 (by decide)) (($variant).textOffset $shape + (suffixOffset $shape $variant)) (suffixLength $shape) (by omega)
        · exact boundary_ne_program $out (by have h := Variant.pc_inProgram $variant (by cases ($variant) <;> (try dsimp only [slotOffset, suffixOffset, suffixLength]) <;> decide : suffixOffset $shape $variant + (suffixLength $shape) < 1024) $shape; simpa [tailDisp, suffixLength, movM8Imm8Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
      apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
      intro s t _ h
      dsimp only [suffixWithRegister, suffixEffect, registerWrites, shiftedBase, slotOffset, tailDisp, suffixLength] at h ⊢
      apply h.weaken
      · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, suffixWithRegister, suffixEffect, registerWrites, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, Variant.pc_add, AddrMode.tail, Disp.bytes]
        all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
      · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, suffixWithRegister, suffixEffect, registerWrites, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, Variant.pc_add, AddrMode.tail, Disp.bytes]
        all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
      · intro i; cases i <;> x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, suffixWithRegister, suffixEffect, registerWrites, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, Variant.pc_add, AddrMode.tail, Disp.bytes]
      · x86_norm [wordRegister_eq_iff, immediateRegister_eq, storeRegister_eq, wordRegister_ne_rsp, rsp_ne_wordRegister, suffixWithRegister, suffixEffect, registerWrites, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, Variant.pc_add, AddrMode.tail, Disp.bytes]
  ))

set_option maxHeartbeats 1000000 in
private theorem runSuffix_slices [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip)  :
    AdvanceTriple boundary (fun s => Pre v s .slices (suffixOffset .slices v))
      (codeRange (v.pc (suffixOffset .slices v) .slices) (suffixBytes v .slices))
      (Effect.post (fun s => suffixWithRegister v s .slices)) := by
  sha512_initialize_suffix_for v, boundary, outside, .slices

set_option maxHeartbeats 1000000 in
private theorem runSuffix_digest [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip)  :
    AdvanceTriple boundary (fun s => Pre v s .digest (suffixOffset .digest v))
      (codeRange (v.pc (suffixOffset .digest v) .digest) (suffixBytes v .digest))
      (Effect.post (fun s => suffixWithRegister v s .digest)) := by
  sha512_initialize_suffix_for v, boundary, outside, .digest

set_option maxHeartbeats 1000000 in
private theorem runSuffix_reset [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (stage : Fin 3) :
    AdvanceTriple boundary (fun s => Pre v s (.reset stage) (suffixOffset (.reset stage) v))
      (codeRange (v.pc (suffixOffset (.reset stage) v) (.reset stage)) (suffixBytes v (.reset stage)))
      (Effect.post (fun s => suffixWithRegister v s (.reset stage))) := by
  sha512_initialize_suffix_for v, boundary, outside, (.reset stage)

set_option maxHeartbeats 1000000 in
private theorem runSuffix_finalizeIntoReset [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (second : Bool) :
    AdvanceTriple boundary (fun s => Pre v s (.finalizeIntoReset second) (suffixOffset (.finalizeIntoReset second) v))
      (codeRange (v.pc (suffixOffset (.finalizeIntoReset second) v) (.finalizeIntoReset second)) (suffixBytes v (.finalizeIntoReset second)))
      (Effect.post (fun s => suffixWithRegister v s (.finalizeIntoReset second))) := by
  sha512_initialize_suffix_for v, boundary, outside, (.finalizeIntoReset second)

set_option maxHeartbeats 1000000 in
private theorem runSuffix_traitFinalizeIntoReset [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (second : Bool) :
    AdvanceTriple boundary (fun s => Pre v s (.traitFinalizeIntoReset second) (suffixOffset (.traitFinalizeIntoReset second) v))
      (codeRange (v.pc (suffixOffset (.traitFinalizeIntoReset second) v) (.traitFinalizeIntoReset second)) (suffixBytes v (.traitFinalizeIntoReset second)))
      (Effect.post (fun s => suffixWithRegister v s (.traitFinalizeIntoReset second))) := by
  sha512_initialize_suffix_for v, boundary, outside, (.traitFinalizeIntoReset second)

theorem runSuffix [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (form : Form) :
    AdvanceTriple boundary (fun s => Pre v s form (suffixOffset form v))
      (codeRange (v.pc (suffixOffset form v) form) (suffixBytes v form))
      (Effect.post (fun s => suffixWithRegister v s form)) := by
  cases form with
  | slices => exact runSuffix_slices boundary outside
  | digest => exact runSuffix_digest boundary outside
  | reset stage => exact runSuffix_reset boundary outside stage
  | finalizeIntoReset second => exact runSuffix_finalizeIntoReset boundary outside second
  | traitFinalizeIntoReset second => exact runSuffix_traitFinalizeIntoReset boundary outside second

set_option maxHeartbeats 1000000 in
private theorem runPrefixSlices [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre v) (codeRange (v.pc 0x11) (bytes v))
      (Effect.post (prefixEffect v)) := by
  advance_begin (mov_m64_r64_effect_step (v.pc 0x11) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel +revert) rfl rfl)
  case sub =>
    have hslice := codeRange_slice_subset (v.pc 0x11) (bytes v) 0 5
    have hbytes : (0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d8 8)).modrm 1 :: (AddrMode.sib 4 none 0 (.d8 8)).tail) = ((bytes v).drop 0).take 5 := by cases v <;> decide +kernel +revert
    rw [hbytes]
    simpa only [BitVec.add_zero] using hslice
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm; exact h.writable (8,8) (by dsimp only [slots, slotOffset]; simp)
    · x86_norm
      simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using h.codeApart (8,8) (by dsimp only [slots, slotOffset]; simp) (v.textOffset + 0x11) 5 (by cases v <;> decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using h.codeApart (8,8) (by dsimp only [slots, slotOffset]; simp) (v.textOffset + 0x11) 191 (by cases v <;> decide)
  case «next» => exact fun _ _ => boundary_ne_program outside (by have h := Variant.pc_inProgram v (by decide : 0x16 < 1024); simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add] using h)
  advance_then (mov_m64_r64_effect_step (v.pc 0x16) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by decide +kernel +revert) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0x11 5]
    have hslice := codeRange_slice_subset (v.pc 0x11) (bytes v) 5 5
    have hbytes : (0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d8 24)).modrm 2 :: (AddrMode.sib 4 none 0 (.d8 24)).tail) = ((bytes v).drop 5).take 5 := by cases v <;> decide +kernel +revert
    rw [hbytes]
    exact hslice
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by change v.pc 0x11 + 5#64 = v.pc 0x16; exact Variant.pc_add v 0x11 5) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (24,8) (by dsimp only [slots, slotOffset]; simp)
    · x86_norm
      simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart (24,8) (by dsimp only [slots, slotOffset]; simp) (v.textOffset + 0x16) 5 (by cases v <;> decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart (24,8) (by dsimp only [slots, slotOffset]; simp) (v.textOffset + 0x11) 191 (by cases v <;> decide)
    · exact boundary_ne_program outside (by have h := Variant.pc_inProgram v (by decide : 0x1b < 1024); simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add] using h)
  advance_then (mov_m64_r64_effect_step (v.pc 0x1b) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel +revert) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0x11 10]
    have hslice := codeRange_slice_subset (v.pc 0x11) (bytes v) 10 5
    have hbytes : (0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d8 16)).modrm 7 :: (AddrMode.sib 4 none 0 (.d8 16)).tail) = ((bytes v).drop 10).take 5 := by cases v <;> decide +kernel +revert
    rw [hbytes]
    exact hslice
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by change v.pc 0x16 + 5#64 = v.pc 0x1b; exact Variant.pc_add v 0x16 5) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (16,8) (by dsimp only [slots, slotOffset]; simp)
    · x86_norm
      simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart (16,8) (by dsimp only [slots, slotOffset]; simp) (v.textOffset + 0x1b) 5 (by cases v <;> decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart (16,8) (by dsimp only [slots, slotOffset]; simp) (v.textOffset + 0x11) 191 (by cases v <;> decide)
    · exact boundary_ne_program outside (by have h := Variant.pc_inProgram v (by decide : 0x20 < 1024); simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add] using h)
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [prefixEffect, Variant.pc_add, AddrMode.tail, Disp.bytes]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prefixEffect, Variant.pc_add, AddrMode.tail, Disp.bytes]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prefixEffect, Variant.pc_add, AddrMode.tail, Disp.bytes]
  · x86_norm [prefixEffect, Variant.pc_add, AddrMode.tail, Disp.bytes]

macro "sha512_prefix_store_first " variant:term "," shape:term "," out:term "," off:term "," len:term "," rex:term "," reg:term "," am:term "," slot:term : tactic =>
  `(tactic| (
    refine Sha2.Proofs.Common.Field.AdvanceTriple.block_first ?k (mov_m64_r64_effect_step (($variant).pc $off $shape) $rex (by simp [RexWPrefix]) $reg $am (by decide +kernel) (by decide +kernel) (by decide +kernel)) ?sub ?pre ?av ?«next»
    case sub =>
      have hb : ($rex :: 0x89 :: ($am).modrm $reg :: ($am).tail) =
          ((prefixBytes $variant $shape).drop ($off - 0x11)).take $len := by
        dsimp only [prefixBytes, argumentBytes, bytes, Variant.textOffset] <;> decide +kernel +revert
      rw [hb]
      have h := codeRange_slice_subset (($variant).pc 0x11 $shape) (prefixBytes $variant $shape) ($off - 0x11) $len
      simpa only [Variant.pc_add, Nat.reduceSub, Nat.reduceAdd] using h
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        simpa [rspOf, Operand.read, gprIndex] using hP.writable ($slot,8) (by dsimp only [slots, slotOffset]; simp)
      · x86_norm
        simpa [prefixBytes, argumentBytes, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart ($slot,8) (by dsimp only [slots, slotOffset]; simp) (($variant).textOffset $shape + $off) $len (by dsimp only [Variant.textOffset]; decide +kernel +revert)
    case av =>
      intro s hP
      apply Effect.avoids_codeRange
      x86_norm
      simpa [prefixBytes, argumentBytes, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart ($slot,8) (by dsimp only [slots, slotOffset]; simp) (($variant).textOffset $shape + 0x11) (prefixBytes $variant $shape).length (by dsimp only [prefixBytes, argumentBytes, bytes, Variant.textOffset] <;> decide +kernel +revert)
    case «next» =>
      intro s hP
      exact boundary_ne_program $out (by
        have h := Variant.pc_inProgram $variant (by decide : $off + $len < 1024) $shape
        simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
    case' k => x86_norm
  ))

macro "sha512_prefix_store_next " variant:term "," shape:term "," out:term "," off:term "," len:term "," rex:term "," reg:term "," am:term "," slot:term : tactic =>
  `(tactic| (
    refine Sha2.Proofs.Common.Field.AdvanceTriple.block_then ?k (mov_m64_r64_effect_step (($variant).pc $off $shape) $rex (by simp [RexWPrefix]) $reg $am (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by x86_local) ?sub ?full ?mid
    case full => x86_full
    case sub =>
      have hb : ($rex :: 0x89 :: ($am).modrm $reg :: ($am).tail) =
          ((prefixBytes $variant $shape).drop ($off - 0x11)).take $len := by
        dsimp only [prefixBytes, argumentBytes, bytes, Variant.textOffset] <;> decide +kernel +revert
      rw [hb]
      have h := codeRange_slice_subset (($variant).pc 0x11 $shape) (prefixBytes $variant $shape) ($off - 0x11) $len
      simpa only [Variant.pc_add, Nat.reduceSub, Nat.reduceAdd] using h
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc_add, Nat.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        simpa [rspOf, Operand.read, gprIndex] using hP.writable ($slot,8) (by dsimp only [slots, slotOffset]; simp)
      · x86_norm
        simpa [prefixBytes, argumentBytes, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart ($slot,8) (by dsimp only [slots, slotOffset]; simp) (($variant).textOffset $shape + $off) $len (by dsimp only [Variant.textOffset]; decide +kernel +revert)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        simpa [prefixBytes, argumentBytes, Variant.pc, rspOf, Operand.read, gprIndex] using hP.codeApart ($slot,8) (by dsimp only [slots, slotOffset]; simp) (($variant).textOffset $shape + 0x11) (prefixBytes $variant $shape).length (by dsimp only [prefixBytes, argumentBytes, bytes, Variant.textOffset] <;> decide +kernel +revert)
      ·
        exact boundary_ne_program $out (by
          have h := Variant.pc_inProgram $variant (by decide : $off + $len < 1024) $shape
          simpa [movM64R64Effect, storeEffect, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
    case' k => x86_norm
  ))

macro "sha512_prefix_register " variant:term "," shape:term "," out:term "," off:term "," len:term "," step:term "," encoded:term : tactic =>
  `(tactic| (
    refine Sha2.Proofs.Common.Field.AdvanceTriple.block_then ?k $step (by x86_local) ?sub ?full ?mid
    case full => x86_full
    case sub =>
      have hb : $encoded = ((prefixBytes $variant $shape).drop ($off - 0x11)).take $len := by
        dsimp only [prefixBytes, argumentBytes, bytes]
        decide +kernel +revert
      change ∀ x ∈ codeRange (($variant).pc $off $shape) $encoded, x ∈ codeRange (($variant).pc 0x11 $shape) (prefixBytes $variant $shape)
      rw [hb]
      have h := codeRange_slice_subset (($variant).pc 0x11 $shape) (prefixBytes $variant $shape) ($off - 0x11) $len
      simpa only [Variant.pc_add, Nat.reduceSub, Nat.reduceAdd] using h
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [Variant.pc_add, Nat.add_assoc]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program $out (by
        have h := Variant.pc_inProgram $variant (by decide : $off + $len < 1024) $shape
        simpa [movR64R64Effect, leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, Variant.pc_add, Nat.add_assoc] using h)
    case' k => x86_norm
  ))

macro "sha512_prefix_end" : tactic =>
  `(tactic| (
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ h
  dsimp only [prefixEffect, suffixOffset] at ⊢
  apply h.weaken
  · x86_norm [prefixEffect, suffixOffset, Variant.pc_add, BitVec.add_zero]
    all_goals repeat' apply And.intro
    all_goals solve_by_elim (maxDepth := 8) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prefixEffect, suffixOffset, Variant.pc_add, BitVec.add_zero]
    all_goals repeat' apply And.intro
    all_goals solve_by_elim (maxDepth := 8) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prefixEffect, suffixOffset, Variant.pc_add, BitVec.add_zero]
  · x86_norm [prefixEffect, suffixOffset, Variant.pc_add, BitVec.add_zero]
  ))

macro "sha512_prefix_finalize_head " variant:term "," shape:term "," out:term : tactic =>
  `(tactic| (
  sha512_prefix_store_first $variant, $shape, $out, 0x11, 8, 0x4c, 0, (AddrMode.sib 4 none 0 (.d32 0xe8)), 0xe8
  sha512_prefix_store_next $variant, $shape, $out, 0x19, 8, 0x48, 1, (AddrMode.sib 4 none 0 (.d32 0xe0)), 0xe0
  sha512_prefix_store_next $variant, $shape, $out, 0x21, 5, 0x48, 2, (AddrMode.sib 4 none 0 (.d8 8)), 8
  ))

macro "sha512_prefix_finalize_full " variant:term "," shape:term "," out:term : tactic =>
  `(tactic| (
  sha512_prefix_finalize_head $variant, $shape, $out
  sha512_prefix_store_next $variant, $shape, $out, 0x26, 4, 0x48, 7, (AddrMode.sib 4 none 0 .none), 0
  sha512_prefix_end
  ))

macro "sha512_prefix_finalize_truncated " variant:term "," shape:term "," out:term : tactic =>
  `(tactic| (
  sha512_prefix_finalize_head $variant, $shape, $out
  sha512_prefix_register $variant, $shape, $out, 0x26, 3, (mov_r64_r64_effect_step (($variant).pc 0x26 $shape) 0x49 0xf7 (by simp [RexWPrefix]) (by decide)), ([0x49,0x89,0xf7] : List UInt8)
  sha512_prefix_store_next $variant, $shape, $out, 0x29, 4, 0x48, 7, (AddrMode.sib 4 none 0 .none), 0
  sha512_prefix_end
  ))

macro "sha512_prefix_trait_other " variant:term "," shape:term "," out:term : tactic =>
  `(tactic| (
  sha512_prefix_store_first $variant, $shape, $out, 0x11, 8, 0x4c, 0, (AddrMode.sib 4 none 0 (.d32 0xf8)), 0xf8
  sha512_prefix_register $variant, $shape, $out, 0x19, 3, (mov_r64_r64_effect_step (($variant).pc 0x19 $shape) 0x48 0xcd (by simp [RexWPrefix]) (by decide)), ([0x48,0x89,0xcd] : List UInt8)
  sha512_prefix_store_next $variant, $shape, $out, 0x1c, 5, 0x48, 2, (AddrMode.sib 4 none 0 (.d8 0x18)), 0x18
  sha512_prefix_store_next $variant, $shape, $out, 0x21, 5, 0x48, 7, (AddrMode.sib 4 none 0 (.d8 0x10)), 0x10
  sha512_prefix_end
  ))

macro "sha512_prefix_trait_wide " variant:term "," shape:term "," out:term : tactic =>
  `(tactic| (
  sha512_prefix_store_first $variant, $shape, $out, 0x11, 8, 0x4c, 0, (AddrMode.sib 4 none 0 (.d32 0xf8)), 0xf8
  sha512_prefix_register $variant, $shape, $out, 0x19, 3, (mov_r64_r64_effect_step (($variant).pc 0x19 $shape) 0x49 0xcd (by simp [RexWPrefix]) (by decide)), ([0x49,0x89,0xcd] : List UInt8)
  sha512_prefix_store_next $variant, $shape, $out, 0x1c, 5, 0x48, 2, (AddrMode.sib 4 none 0 (.d8 0x18)), 0x18
  sha512_prefix_store_next $variant, $shape, $out, 0x21, 5, 0x48, 7, (AddrMode.sib 4 none 0 (.d8 0x10)), 0x10
  sha512_prefix_end
  ))

macro "sha512_prefix_reset " variant:term "," shape:term "," out:term : tactic =>
  `(tactic| (
  sha512_prefix_store_first $variant, $shape, $out, 0x11, 8, 0x4c, 0, (AddrMode.sib 4 none 0 (.d32 0xf0)), 0xf0
  sha512_prefix_store_next $variant, $shape, $out, 0x19, 8, 0x48, 1, (AddrMode.sib 4 none 0 (.d32 0xe8)), 0xe8
  sha512_prefix_store_next $variant, $shape, $out, 0x21, 8, 0x48, 2, (AddrMode.sib 4 none 0 (.d32 0xe0)), 0xe0
  sha512_prefix_register $variant, $shape, $out, 0x29, 3, (mov_r64_r64_effect_step (($variant).pc 0x29 $shape) 0x49 0xf4 (by simp [RexWPrefix]) (by decide)), ([0x49,0x89,0xf4] : List UInt8)
  sha512_prefix_store_next $variant, $shape, $out, 0x2c, 8, 0x48, 7, (AddrMode.sib 4 none 0 (.d32 0xd8)), 0xd8
  sha512_prefix_register $variant, $shape, $out, 0x34, 8, (lea_r64_effect_step (($variant).pc 0x34 $shape) 0x48 (by simp [RexWPrefix]) 0 (AddrMode.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)), ([0x48,0x8d,0x84,0x24,0x80,0,0,0] : List UInt8)
  sha512_prefix_end
  ))

set_option maxHeartbeats 1000000 in
private theorem runPrefix_reset [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (stage : Fin 3) :
    AdvanceTriple boundary (fun s => Pre v s (.reset stage) 0x11)
      (codeRange (v.pc 0x11 (.reset stage)) (prefixBytes v (.reset stage)))
      (Effect.post (fun s => prefixEffect v s (.reset stage))) := by
  cases v with
  | sha384 => sha512_prefix_reset (Variant.sha384), (.reset stage), outside
  | sha512 => sha512_prefix_reset (Variant.sha512), (.reset stage), outside
  | sha512_224 => sha512_prefix_reset (Variant.sha512_224), (.reset stage), outside
  | sha512_256 => sha512_prefix_reset (Variant.sha512_256), (.reset stage), outside

set_option maxHeartbeats 1000000 in
private theorem runPrefix_finalize [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (second : Bool) :
    AdvanceTriple boundary (fun s => Pre v s (.finalizeIntoReset second) 0x11)
      (codeRange (v.pc 0x11 (.finalizeIntoReset second)) (prefixBytes v (.finalizeIntoReset second)))
      (Effect.post (fun s => prefixEffect v s (.finalizeIntoReset second))) := by
  cases v with
  | sha384 => sha512_prefix_finalize_full (Variant.sha384), (.finalizeIntoReset second), outside
  | sha512 => sha512_prefix_finalize_full (Variant.sha512), (.finalizeIntoReset second), outside
  | sha512_224 => sha512_prefix_finalize_truncated (Variant.sha512_224), (.finalizeIntoReset second), outside
  | sha512_256 => sha512_prefix_finalize_truncated (Variant.sha512_256), (.finalizeIntoReset second), outside

set_option maxHeartbeats 1000000 in
private theorem runPrefix_trait [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (second : Bool) :
    AdvanceTriple boundary (fun s => Pre v s (.traitFinalizeIntoReset second) 0x11)
      (codeRange (v.pc 0x11 (.traitFinalizeIntoReset second)) (prefixBytes v (.traitFinalizeIntoReset second)))
      (Effect.post (fun s => prefixEffect v s (.traitFinalizeIntoReset second))) := by
  cases v with
  | sha384 => sha512_prefix_trait_other (Variant.sha384), (.traitFinalizeIntoReset second), outside
  | sha512 => sha512_prefix_trait_wide (Variant.sha512), (.traitFinalizeIntoReset second), outside
  | sha512_224 => sha512_prefix_trait_other (Variant.sha512_224), (.traitFinalizeIntoReset second), outside
  | sha512_256 => sha512_prefix_trait_other (Variant.sha512_256), (.traitFinalizeIntoReset second), outside

theorem runPrefix [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) {form : Form} :
    AdvanceTriple boundary (fun s => Pre v s form 0x11)
      (codeRange (v.pc 0x11 form) (prefixBytes v form))
      (Effect.post (fun s => prefixEffect v s form)) := by
  cases form with
  | slices => exact runPrefixSlices boundary outside
  | reset stage => exact runPrefix_reset boundary outside stage
  | finalizeIntoReset second => exact runPrefix_finalize boundary outside second
  | traitFinalizeIntoReset second => exact runPrefix_trait boundary outside second
  | digest =>
    intro s ready loaded pre
    refine ⟨0, s, (advances_zero boundary s s).2 rfl, ready, loaded, ?_⟩
    exact ⟨pre.rip, trivial, trivial, AgreesExcept.refl _ _⟩

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) {form : Form} :
    AdvanceTriple boundary (fun s => Pre v s form)
      (codeRange (v.pc (startOffset form v) form) (bytes v form))
      (Effect.post (fun s => effectWithRegister v s form)) := by
  have programBound : v.textOffset + 0x11 + 191 ≤ 71757 := by cases v <;> decide
  cases form with
  | digest =>
    simpa only [suffixBytes, suffixOffset, startOffset, Nat.sub_self, List.drop_zero,
      effectWithRegister, effect, List.nil_append, suffixWithRegister] using
      runSuffix (v := v) boundary outside (.digest)
  | reset stage =>
    simpa only [suffixBytes, suffixOffset, startOffset, Nat.sub_self, List.drop_zero,
      effectWithRegister, effect, List.nil_append, suffixWithRegister] using
      runSuffix (v := v) boundary outside (.reset stage)
  | finalizeIntoReset second =>
    simpa only [suffixBytes, suffixOffset, startOffset, Nat.sub_self, List.drop_zero,
      effectWithRegister, effect, List.nil_append, suffixWithRegister] using
      runSuffix (v := v) boundary outside (.finalizeIntoReset second)
  | traitFinalizeIntoReset second =>
    simpa only [suffixBytes, suffixOffset, startOffset, Nat.sub_self, List.drop_zero,
      effectWithRegister, effect, List.nil_append, suffixWithRegister] using
      runSuffix (v := v) boundary outside (.traitFinalizeIntoReset second)
  | slices =>
    intro s ready loaded pre
    obtain ⟨n, t, steps, readyT, loadedT, hp⟩ :=
      runPrefix boundary outside s ready loaded pre
    have hrsp : rspOf t = rspOf s := by
      have ho := hp.obsAfter (by simp [prefixEffect, Write.Full, Operand.Full])
      have hr := (ho true).read_reg (n := 64) 4
      x86_norm [prefixEffect] at hr
      simpa [rspOf, Operand.read, gprIndex] using hr.symm
    have preT : Pre v t .slices (suffixOffset .slices) := by
      refine ⟨hp.rip, ?_, ?_⟩
      · intro slot hm
        rw [hrsp]
        exact (pre.writable slot hm).of_holds hp
      · intro slot hm offset len bound
        rw [hrsp]
        exact pre.codeApart slot hm offset len bound
    have sub : ∀ x ∈ codeRange (v.pc (suffixOffset .slices))
        (suffixBytes v .slices), x ∈ codeRange (v.pc 0x11) (bytes v) := by
      have h := codeRange_slice_subset (v.pc 0x11) (bytes v) 15 176
      rw [List.take_of_length_le (by rw [List.length_drop, bytes_length]; decide)] at h
      simpa only [suffixBytes, suffixOffset, startOffset, Variant.pc_add] using h
    obtain ⟨m, u, steps', readyU, _, hs⟩ :=
      runSuffix boundary outside .slices t readyT (loadedT.mono sub) preT
    have combined := hp.seq (e₁ := fun s => prefixEffect v s .slices) (e₂ := fun s => suffixWithRegister v s .slices)
      (by
        apply Sha2.Proofs.Common.EffectCompose.Effect.Local.of_eq
        · intro a b ho
          have hr := ho.read_reg (n := 64) 4
          simp only [suffixWithRegister, suffixEffect, rspOf, Operand.read, gprIndex] at hr ⊢
          rw [hr]
        · intro a
          simp [suffixWithRegister, suffixEffect, registerWrites, Write.Full, Operand.Full])
      (by simp [prefixEffect, Write.Full, Operand.Full]) hs
    have result : (effectWithRegister v s).Holds s u := by
      apply combined.weaken
      all_goals dsimp only [prefixEffect, suffixWithRegister, suffixEffect, effectWithRegister, effect, registerWrites, slotOffset, suffixOffset]
      · x86_norm [prefixEffect, suffixWithRegister, suffixEffect, effectWithRegister,
          effect, Variant.pc_add]
        all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
      · x86_norm [prefixEffect, suffixWithRegister, suffixEffect, effectWithRegister,
          effect, Variant.pc_add]
        all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
      · intro i; cases i <;> x86_norm [prefixEffect, suffixWithRegister, suffixEffect,
          effectWithRegister, effect, Variant.pc_add]
      · x86_norm [prefixEffect, suffixWithRegister, suffixEffect, effectWithRegister,
          effect, Variant.pc_add]
    refine ⟨n + m, u, steps.trans steps', readyU, result.codeIn ?_ loaded, result⟩
    apply Effect.avoids_codeRange
    dsimp only [effectWithRegister, effect, prefixEffect, suffixEffect, registerWrites, slotOffset, suffixOffset]
    x86_norm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (8,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (24,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (16,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (424,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (416,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (408,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (400,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (392,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (384,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (376,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (368,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (440,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (432,8) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound
    · simpa [startOffset, bytes_length, Variant.pc, rspOf, Operand.read, gprIndex] using
        pre.codeApart (367,1) (by dsimp only [slots, slotOffset]; simp)
          (v.textOffset + 0x11) 191 programBound

end Sha2.Proofs.Wrapper512.Dispatch.Store
