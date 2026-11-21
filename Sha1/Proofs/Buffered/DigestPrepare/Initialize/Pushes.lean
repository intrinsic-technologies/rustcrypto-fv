import Sha1.Proofs.Buffered.DigestPrepare.Initialize.Model

namespace Sha1.Proofs.Buffered.DigestPrepare.Initialize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read pushAddr pushR64Effect pushEffect
  BitVec.sub_eq_add_neg

private theorem pushR64Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (pushR64Effect p len src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [pushR64Effect, pushEffect, pushAddr, stackPtr_read, h.read_reg]
  · exact congrArg some hi
  · simp [pushR64Effect, pushEffect, Write.Full, Operand.Full]

attribute [local x86_local] pushR64Effect_local

def pushEffect (s : RamState) : Effect where
  rip := 0x100017
  writes :=
    [⟨(.mem (stackPtr s - 8) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 16) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
     ⟨(.reg 4 : Operand 64), stackPtr s - 32⟩,
     ⟨(.mem (stackPtr s - 32) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]

macro "push_mid " offset:term "," sub:term "," isub:term : tactic => `(tactic| (
  intro s t h hE hO
  have hsp : pushAddr t = stackPtr s - BitVec.ofNat 64 $offset := by
    rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
    x86_norm
  refine ⟨⟨hE.rip, ?_, ?_⟩, ?_⟩
  · rw [hsp]
    exact memWritable_of_holds hE (h.writable $offset 8 (by decide +kernel) (by decide))
  · rw [hsp]
    simpa only [Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
      Bytes.Chunked.toListFrom, List.length_map, List.length_range'] using
      h.apart $offset 8 (by decide +kernel) (by decide) _ _ $isub
  · intro x hx c hc hcov
    have hrange := h.avoids_mem $offset 8 (by decide +kernel) (by decide)
    have hsub := $sub
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc <;> subst c
    · exact hcov
    · rw [hsp] at hcov
      exact hrange x (hsub x hx) hcov
    · exact hcov))

set_option maxRecDepth 2048 in
theorem pushes [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x100010 Digest.minStackBytes)
      (codeRange 0x100010 [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53]) pushEffect := by
  have hSub := prologue_text_sub 0x10 7 (by decide +kernel)
  md5_run_begin (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step 0x100010 0x41 0x57
    (by unfold RexPrefix; decide) (by decide))
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 8 8 (by decide +kernel) (by decide), ?_⟩
    simpa only [pushAddr, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
      Bytes.Chunked.toListFrom, List.length_map, List.length_range'] using
      h.apart 8 8 (by decide +kernel) (by decide) _ _
        (prologue_text_sub 0x10 2 (by decide +kernel))
  case av =>
    intro s h x hx c hc hcov
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact h.avoids_mem 8 8 (by decide +kernel) (by decide) x (hSub x hx) hcov
    · exact hcov
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x12 (by decide +kernel)
  md5_run_then (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step 0x100012 0x41 0x56
    (by unfold RexPrefix; decide) (by decide))
  case mid => push_mid 16, hSub, (prologue_text_sub 0x12 2 (by decide +kernel))
  case sub => exact codeRange_mem_of_drop (p := 0x100010) 2 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14 (by decide +kernel)
  md5_run_then (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step 0x100014 0x41 0x54
    (by unfold RexPrefix; decide) (by decide))
  case mid => push_mid 24, hSub, (prologue_text_sub 0x14 2 (by decide +kernel))
  case sub => exact codeRange_mem_of_drop (p := 0x100010) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x16 (by decide +kernel)
  md5_run_then (Sha1.Proofs.Common.Instructions.MovStore.push_r64_effect_step 0x100016 0x53 (by decide))
  case mid => push_mid 32, hSub, (prologue_text_sub 0x16 1 (by decide +kernel))
  case sub => exact codeRange_mem_of_drop (p := 0x100010) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x17 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [pushEffect]
  · x86_norm [pushEffect]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [pushEffect]
  · x86_norm [pushEffect]

set_option maxRecDepth 2048 in
theorem pushes_frame {s t : RamState}
    (h : PrologueFrame 0x100010 Digest.minStackBytes s)
    (he : (pushEffect s).Holds s t) : PrologueFrame 0x100017 624 t := by
  have hrsp : stackPtr t = stackPtr s - 32 := he.writes.2.2.2.1
  have hn : (stackPtr t).toNat = (stackPtr s).toNat - 32 := by
    rw [hrsp]
    exact h.slot_toNat 32 (by decide +kernel)
  have hl : 656 ≤ (stackPtr s).toNat := h.stack.2.2.1
  have hb : (stackPtr s).toNat - 656 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 656)) < 2^32 := h.stack.1
  have hc : ∀ a, (Stack.region t 624).Contains a →
      (Stack.region s Digest.minStackBytes).Contains a := by
    intro a ha
    change (stackPtr t).toNat - 624 ≤ a ∧ a < (stackPtr t).toNat - 624 +
      ((stackPtr t).toNat + 8 - ((stackPtr t).toNat - 624)) at ha
    change (stackPtr s).toNat - 656 ≤ a ∧ a < (stackPtr s).toNat - 656 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 656))
    rw [hn] at ha
    omega
  refine ⟨he.rip, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · change (stackPtr t).toNat - 624 +
      ((stackPtr t).toNat + 8 - ((stackPtr t).toNat - 624)) < userAddressLimit
    rw [hn]
    change _ < 2^32
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp
      (he.agrees.grow _ (Option.isSome_iff_exists.mpr (h.stack.2.1 a (hc a.toNat ha))))
  · change 624 ≤ (stackPtr t).toNat
    omega
  · have ha : (stackPtr s).toNat % 16 = 8 := h.stack.2.2.2
    change (stackPtr t).toNat % 16 = 8
    omega
  · intro a ha
    exact h.avoids a (hc a.toNat ha)

theorem pushes_avoids {s : RamState} (h : PrologueFrame 0x100010 Digest.minStackBytes s) :
    (pushEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [pushEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim hcov
    | exact h.avoids_mem 8 8 (by decide +kernel) (by decide) x hx hcov
    | exact h.avoids_mem 16 8 (by decide +kernel) (by decide) x hx hcov
    | exact h.avoids_mem 24 8 (by decide +kernel) (by decide) x hx hcov
    | exact h.avoids_mem 32 8 (by decide +kernel) (by decide) x hx hcov

end Sha1.Proofs.Buffered.DigestPrepare.Initialize
