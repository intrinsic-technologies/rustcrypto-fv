import Md5.Proofs.Streaming.Prologue

namespace Md5.Proofs.NewEntries.UpdateFinalize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs Md5.Proofs.Block Md5.Proofs.Streaming

structure SlicesProloguePost (initial : RamState) (inputs : Array Slices.Input)
    (final : RamState) : Prop extends
    PrologueCommon 280 192 168 176 184 OneMessage.updateFinalizeInto.minStackBytes .rcx initial final where
  rip : final.RIP = if inputs.size = 0 then 0x1019db else 0x1018ed
  index : inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read final = 0
  count : inputs.size ≠ 0 →
    (Operand.reg 12 : Operand 64).read final = BitVec.ofNat 64 inputs.size

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read pushAddr pushR64Effect pushEffect
  BitVec.sub_eq_add_neg

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_compose] movM8Imm8Effect subR64Imm32Effect
attribute [local x86_local] movM8Imm8Effect_local

def slicesInitBytes : List UInt8 := [
    0x48, 0x81, 0xec, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8c, 0x24, 0xa8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xbc, 0x24, 0xb0,
    0x00, 0x00, 0x00, 0x48, 0xb8, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0x48,
    0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0xb8, 0x01, 0x23, 0x45, 0x67, 0x89,
    0xab, 0xcd, 0xef, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xc7, 0x84,
    0x24, 0x10, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x84, 0x24, 0xff, 0x00,
    0x00, 0x00, 0x00]

def slicesInitEffect (s : RamState) : Effect where
  rip := 0x1018a1
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 280⟩,
     ⟨(.mem (stackPtr s - 112) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 96) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 104) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 16) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.reg 0 : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 8) : Operand 64), 0⟩,
     ⟨(.mem (stackPtr s - 25) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem slices_initialize [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x10184a 600)
      (codeRange 0x10184a slicesInitBytes) slicesInitEffect := by
  have hSub := prologue_text_sub 0x184a 87 (by decide +kernel)
  unfold slicesInitBytes
  have hFirst := sub_r64_imm32_effect_step 0x10184a 0x48 0xec 280
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (subR64Imm32Effect 0x10184a 4 280) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1851 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101851 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 168))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 7 (by decide +kernel)
  case mid => init_store_mid 112, 8, (prologue_text_sub 0x1851 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1859 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101859 0x48
    (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 184))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 15 (by decide +kernel)
  case mid => init_store_mid 96, 8, (prologue_text_sub 0x1859 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1861 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101861 0x48
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 176))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 23 (by decide +kernel)
  case mid => init_store_mid 104, 8, (prologue_text_sub 0x1861 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1869 (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x101869 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 31 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1873 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101873 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 264))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 41 (by decide +kernel)
  case mid => init_store_mid 16, 8, (prologue_text_sub 0x1873 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x187b (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x10187b 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 49 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1885 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101885 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 256))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 59 (by decide +kernel)
  case mid => init_store_mid 24, 8, (prologue_text_sub 0x1885 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x188d (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_imm32_effect_step 0x10188d 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 272))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 67 (by decide +kernel)
  case mid => init_store_mid 8, 8, (prologue_text_sub 0x188d 12 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1899 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m8_imm8_effect_step 0x101899
    (.sib 4 none 0 (.d32 255)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10184a) 79 (by decide +kernel)
  case mid => init_store_mid 25, 1, (prologue_text_sub 0x1899 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x18a1 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [slicesInitEffect]
  · x86_norm [slicesInitEffect]
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · intro i; cases i <;> x86_norm [slicesInitEffect]
  · x86_norm [slicesInitEffect]

private theorem slicesInitEffect_local : Effect.Local slicesInitEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [slicesInitEffect, stackPtr_read, h.read_reg]
  · cases i <;> rfl
  · simp [slicesInitEffect, Write.Full, Operand.Full]

theorem slicesInitEffect_avoids {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 112 ≤ budget) :
    (slicesInitEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [slicesInitEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact h.avoids_mem 112 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 96 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 104 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 16 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 24 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 8 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 25 1 (by omega) (by decide) x hx hcov

theorem slices_initialized [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x101840 OneMessage.updateFinalizeInto.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (Effect.seq (prologuePushEffect 0x101840) slicesInitEffect s).Holds s t := by
  obtain ⟨n, u, hPush, hu, _, hEPush⟩ :=
    prologue_pushes boundary 0x101840 OneMessage.updateFinalizeInto.minStackBytes (by decide +kernel)
      (prologue_text_sub 0x1840 10 (by decide +kernel))
      (prologue_boundary boundary hOutside 0x1840 (by decide +kernel))
      s hReady (program_text_slice hCode 0x1840 10 (by decide +kernel)) hFrame
  have hCodeU := hEPush.codeIn (prologuePushEffect_avoids hFrame (by decide +kernel)) hCode
  have hFrameU : PrologueFrame 0x10184a 600 u :=
    hFrame.after_pushes (by decide +kernel) hEPush
  obtain ⟨m, t, hInit, ht, _, hEInit⟩ :=
    slices_initialize boundary hOutside u hu
      (program_text_slice hCodeU 0x184a 87 (by decide +kernel)) hFrameU
  refine ⟨n + m, t, hPush.trans hInit, ht,
    hEInit.codeIn (slicesInitEffect_avoids hFrameU (by decide)) hCodeU, ?_⟩
  exact hEPush.seq slicesInitEffect_local
    (by simp [prologuePushEffect, Write.Full, Operand.Full]) hEInit

theorem slices_initialized_common {s t : RamState}
    (hFrame : PrologueFrame 0x101840 OneMessage.updateFinalizeInto.minStackBytes s)
    (hE : (Effect.seq (prologuePushEffect 0x101840) slicesInitEffect s).Holds s t) :
    PrologueCommon 280 192 168 176 184 OneMessage.updateFinalizeInto.minStackBytes .rcx s t := by
  have hWrites := hE.writes
  x86_norm [prologuePushEffect, slicesInitEffect] at hWrites
  rcases hWrites with ⟨h5, h15, h14, h13, h12, h3, hsp, hout, hlen, hptr,
    hhigh, hax, hlow, hblocks, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 328 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hAgrees : AgreesExcept (prologueChanges s OneMessage.updateFinalizeInto.minStackBytes) s t := by
    apply hE.agrees.widen
    · intro c hc hm
      cases c with
      | reg r =>
        x86_norm [prologuePushEffect, slicesInitEffect] at hc
        rcases hc with rfl | rfl <;> simp [prologueChanges]
      | mem a len => cases hm
      | flags => simp [prologueChanges]
      | rip => simp [prologueChanges]
      | _ => x86_norm [prologuePushEffect, slicesInitEffect] at hc
    · intro address c hc hcov
      have hContains : (⟨(Stack.region s OneMessage.updateFinalizeInto.minStackBytes).start,
          OneMessage.updateFinalizeInto.minStackBytes⟩ : MemoryRegion).Contains address.toNat := by
        x86_norm [prologuePushEffect, slicesInitEffect] at hc
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c
        · apply hFrame.covers_in_stack 8 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 16 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 24 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 32 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 40 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 48 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 160 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 144 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 152 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 64 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 72 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 56 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 73 1 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · exact False.elim hcov
      exact ⟨.mem (BitVec.ofNat 64 (Stack.region s OneMessage.updateFinalizeInto.minStackBytes).start)
        OneMessage.updateFinalizeInto.minStackBytes,
        by simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false, or_true],
        prologue_covers_of_contains
          (region := ⟨(Stack.region s OneMessage.updateFinalizeInto.minStackBytes).start,
            OneMessage.updateFinalizeInto.minStackBytes⟩) hContains⟩
  refine {
    rsp := hRsp
    absorbed := ?absorbed
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    agrees := hAgrees
    memoryFrame := ?memoryFrame
  }
  case absorbed =>
    apply absorbed_empty_of_initial_words (stackPtr t + 192)
    · have hr := (hFrame.writable 72 16 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 72) 16 :=
        ⟨hr.low, fun i hi ↦ hE.agrees.grow _ (hr.mem i hi)⟩
      simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using ht
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlow
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hhigh
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hposition
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hblocks
  case saved =>
    intro i
    finite_cases i
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[0] = 3#5 from by decide +kernel]
        using h3
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[1] = 12#5 from by decide +kernel]
        using h12
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[2] = 13#5 from by decide +kernel]
        using h13
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[3] = 14#5 from by decide +kernel]
        using h14
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[4] = 15#5 from by decide +kernel]
        using h15
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[5] = 5#5 from by decide +kernel]
        using h5
  case output =>
    change (Operand.mem (stackPtr t + 168) : Operand 64).read t =
      (Operand.reg 1 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hout
  case pointer =>
    change (Operand.mem (stackPtr t + 176) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hptr
  case length =>
    change (Operand.mem (stackPtr t + 184) : Operand 64).read t =
      (Operand.reg 2 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlen
  case returnSlot =>
    simpa only [hRsp, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceAdd]
      using prologue_return_read hFrame hAgrees
  case memoryFrame => exact prologue_memoryFrame hFrame hAgrees

private theorem prologueJmpEffect_local {p : BitVec 64} {len : Nat} {offset : BitVec 64} :
    Effect.Local (fun _ ↦ jmpEffect p len offset) := by
  refine ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    fun _ _ _ i hi ↦ congrArg some hi, ?_⟩
  intro t w hw
  cases hw

attribute [local x86_local] prologueJmpEffect_local
attribute [local x86_compose] jmpEffect branchTarget decR64Effect incR64Effect

def slicesNonemptyEffect (s : RamState) : Effect where
  rip := 0x1018ed
  writes := [⟨(.reg 12 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
    ⟨(.reg 15 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem slices_nonempty_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1018aa)
      (codeRange 0x1018aa [0x49, 0x89, 0xf4, 0x45, 0x31, 0xff, 0xeb, 0x3b])
      slicesNonemptyEffect := by
  md5_run_begin (mov_r64_r64_effect_step 0x1018aa 0x49 0xf4
    (by unfold RexWPrefix; decide) (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x18ad (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x1018ad 0x45 0xff
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1018aa) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x18b0 (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x1018b0 0x3b (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x1018aa) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x18ed (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [slicesNonemptyEffect]
  · x86_norm [slicesNonemptyEffect]
    constructor
    · rfl
    · change (0 : BitVec 64) =
        (((Operand.reg 15 : Operand 32).read s) ^^^ (Operand.reg 15 : Operand 32).read s).setWidth 64
      simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [slicesNonemptyEffect]
  · x86_norm [slicesNonemptyEffect]

theorem slices_branch [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1018a1) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (Operand.reg 6 : Operand 64).read s = 0 then 0x1019db else 0x1018ed) ∧
      AgreesExcept [.reg 12, .reg 15, .flags, .rip] s t ∧
      ((Operand.reg 6 : Operand 64).read s ≠ 0 →
        (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s ∧
        (Operand.reg 15 : Operand 64).read t = 0) := by
  obtain ⟨u, hTest, hu, hETest⟩ :=
    (test_r64_r64_effect_step 0x1018a1 0x48 0xf6
      (by unfold RexWPrefix; decide) (by decide)).advances hReady
      (program_text_slice hCode 0x18a1 3 (by decide +kernel)) hRip
      (text_address_ne_return hOutside 0x18a4 (by decide +kernel))
  change (testR64R64Effect 0x1018a1 6 6 s).Holds s u at hETest
  have hCodeU := hETest.codeIn (testR64R64Effect_avoids _ _ _ _ _) hCode
  have hZF : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      decide ((Operand.reg 6 : Operand 64).read s = 0) := by
    simpa only [Effect.flag, testR64R64Effect, testFlags, StatusFlagsOutcome.get,
      StatusFlags.get, BitVec.and_self, FlagAllows, Bool.beq_eq_decide_eq] using hETest.flag .ZF
  obtain ⟨v, hJump, hv, hEJump⟩ :=
    (jcc_rel32_effect_step 0x1018a4 4 0x131).advances hu
      (program_text_slice hCodeU 0x18a4 6 (by decide +kernel))
      ⟨hETest.rip, fun _ ↦ by decide +kernel⟩ (by
        change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x1019db else 0x1018aa) ≠ boundary.rip
        split
        · exact text_address_ne_return hOutside 0x19db (by decide +kernel)
        · exact text_address_ne_return hOutside 0x18aa (by decide +kernel))
  have hCodeV := hEJump.codeIn (branchEffect_avoids _ _ _ _) hCodeU
  have hBase : AgreesExcept [.flags, .rip] s v :=
    (hETest.agrees.trans hEJump.agrees).mono (by
      simp [testR64R64Effect, jccEffect, branchEffect, Effect.components])
  have hRipV := hEJump.rip
  change v.RIP = if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x1019db else 0x1018aa at hRipV
  rw [hZF] at hRipV
  by_cases hEmpty : (Operand.reg 6 : Operand 64).read s = 0
  · refine ⟨2, v, hTest.trans hJump, hv, hCodeV, ?_, hBase.mono (by simp), ?_⟩
    · simpa only [hEmpty, decide_true, ite_true] using hRipV
    · intro h; exact False.elim (h hEmpty)
  · have hRipV' : v.RIP = 0x1018aa := by
      simpa only [hEmpty, decide_false, Bool.false_eq_true, ite_false] using hRipV
    obtain ⟨fuel, t, hTail, ht, _, hETail⟩ :=
      slices_nonempty_branch boundary hOutside v hv
        (program_text_slice hCodeV 0x18aa 8 (by decide +kernel)) hRipV'
    have hAgrees : AgreesExcept [.reg 12, .reg 15, .flags, .rip] s t :=
      (hBase.trans hETail.agrees).mono (by simp [slicesNonemptyEffect, Effect.components])
    refine ⟨2 + fuel, t, (hTest.trans hJump).trans hTail, ht,
      hETail.codeIn (Effect.Avoids.of_noMem (by
        simp [slicesNonemptyEffect, Effect.components, Component.Covers]) _) hCodeV,
      ?_, hAgrees, ?_⟩
    · simpa only [hEmpty, ite_false, slicesNonemptyEffect] using hETail.rip
    · intro _
      have hW := hETail.writes
      change (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read v ∧
        (Operand.reg 15 : Operand 64).read t = 0 at hW
      exact ⟨hW.1.trans (hBase.read (by simp)), hW.2⟩

theorem slices_prologue_of_ready [bindings : Bindings] {s : RamState}
    {inputs : Array Slices.Input} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hCall : (OneMessage.ValidCall OneMessage.updateFinalizeInto) bindings s inputs)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ SlicesProloguePost s inputs t := by
  have hFrame : PrologueFrame 0x101840 OneMessage.updateFinalizeInto.minStackBytes s :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable, (hCall.stackSeparation.2 (Stack.region s OneMessage.updateFinalizeInto.minStackBytes) (by simp)).2⟩
  obtain ⟨n, u, hInit, hu, hCodeU, hE⟩ :=
    slices_initialized boundary hReady hCode hFrame hOutside
  have hCommon := slices_initialized_common hFrame hE
  obtain ⟨m, t, hBranch, ht, hCodeT, hRip, hAgrees, hNonempty⟩ :=
    slices_branch boundary hu hCodeU hE.rip hOutside
  have hCountPreserved : (Operand.reg 6 : Operand 64).read u =
      (Operand.reg 6 : Operand 64).read s :=
    hCommon.agrees.read (by simp [prologueChanges])
  have hCountNat : ((Operand.reg 6 : Operand 64).read u).toNat = inputs.size :=
    (congrArg BitVec.toNat hCountPreserved).trans hCall.inputsInMemory.countArgument
  have hZero : (Operand.reg 6 : Operand 64).read u = 0 ↔ inputs.size = 0 := by
    constructor
    · intro hz
      rw [hz] at hCountNat
      exact hCountNat.symm
    · intro hz
      apply BitVec.eq_of_toNat_eq
      exact hCountNat.trans hz
  have hCountValue : (Operand.reg 6 : Operand 64).read u = BitVec.ofNat 64 inputs.size := by
    have hh := congrArg (BitVec.ofNat 64) hCountNat
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh
  refine ⟨n + m, t, hInit.trans hBranch, ht, hCodeT, ?_⟩
  refine {
    toPrologueCommon := hCommon.of_registers (hAgrees.mono (by simp [prologueTailChanges]))
    rip := ?rip
    index := ?index
    count := ?count
  }
  case rip => simpa only [hZero] using hRip
  case index => intro h; exact (hNonempty (fun hz ↦ h (hZero.mp hz))).2
  case count => intro h; exact (hNonempty (fun hz ↦ h (hZero.mp hz))).1.trans hCountValue

theorem slices_prologue (bindings : Bindings) {s : RamState}
    {inputs : Array Slices.Input} (boundary : ReturnBoundary)
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hCall : (OneMessage.ValidCall OneMessage.updateFinalizeInto) bindings s inputs)
    (hOutside : ¬ InProgram boundary.rip) :
    letI := bindings
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ SlicesProloguePost s inputs t := by
  letI := bindings
  have hEntry := Md5.Proofs.entryReady bindings hBindings hMachine hCall.programLoaded
  exact slices_prologue_of_ready boundary hEntry.ready hEntry.code hCall hOutside

end Md5.Proofs.NewEntries.UpdateFinalize
