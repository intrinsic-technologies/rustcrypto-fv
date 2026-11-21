import Md5.Proofs.Buffered.Update.ResetFirst.KindMachine
import Md5.Proofs.Buffered.Update.Counter
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Buffered.ResetFirst
open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] partialCompressEffect_of_kind
theorem partialCompressEffect_local_of_kind (kind : UpdateKind) : Effect.Local (partialCompressEffect_of_kind kind) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [partialCompressEffect_of_kind, stackPtr, h.gpr]
  · simpa only [partialCompressEffect_of_kind, Effect.flag] using congrArg some hi
  · simp [partialCompressEffect_of_kind, Write.Full, Operand.Full]

def incrementPrepareEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := pc kind 0x718
    writes := [⟨(.mem (stackPtr s + stackOffset kind 88) : Operand 64),
      (.mem (stackPtr s + stackOffset kind 88) : Operand 64).read s + 1⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + stackOffset kind 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + stackOffset kind 8⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem increment_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = pc kind 0x704)
    (hw : MemoryRoutines.WritableRange s (stackPtr s + stackOffset kind 88) 8) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (incrementPrepareEffect_of_kind kind s).Holds s t := by
  let am := AddrMode.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 80)))
  have hs := Update.Counter.inc_m64_effect_step (pc kind 0x704) 0x48
    (by unfold RexWPrefix; decide) am (by rcases hk with rfl | rfl | rfl <;> decide) (by rcases hk with rfl | rfl | rfl <;> decide) (by rcases hk with rfl | rfl | rfl <;> decide)
  have hb : CodeIn (codeRange (pc kind 0x704) (0x48 :: 0xff :: am.modrm 0 :: am.tail)) s := by
    rcases hk with rfl | rfl | rfl
    · have hb : (0x48 :: 0xff :: am.modrm 0 :: am.tail) = [0x48,0xff,0x44,0x24,0x58] := by decide +kernel
      rw [hb]
      exact program_text_slice hc 0x704 5 (by decide +kernel)
    · have hb : (0x48 :: 0xff :: am.modrm 0 :: am.tail) = [0x48,0xff,0x44,0x24,0x58] := by decide +kernel
      rw [hb]
      exact program_text_slice hc 0xdb4 5 (by decide +kernel)
    · have hb : (0x48 :: 0xff :: am.modrm 0 :: am.tail) = [0x48,0xff,0x44,0x24,0x70] := by decide +kernel
      rw [hb]
      exact program_text_slice hc 0x143d 5 (by decide +kernel)
  have hp : Memory.StorePre (pc kind 0x704) (3 + am.tail.length)
      (storeAddrAt (pc kind 0x704) am (3 + am.tail.length)) 8 s := by
    refine ⟨hip, ?_, ?_⟩
    · rcases hk with rfl | rfl | rfl <;> x86_norm [am, stackOffset, UpdateKind.contextOffset] at *
      all_goals exact ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
    · rcases hk with rfl | rfl | rfl <;> x86_norm [am, stackOffset, UpdateKind.contextOffset]
      all_goals
        intro i hi j hj heq
        apply hw.code i hi
        simp only [Operand.read_reg64] at heq
        x86_norm [stackPtr, stackOffset, UpdateKind.contextOffset] at heq ⊢
        rw [heq]
      · have ht := text_address_in_program (0x704+j) (by
        have hn : 0x709 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
      · have ht := text_address_in_program (0xdb4+j) (by
        have hn : 0xdb9 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
      · have ht := text_address_in_program (0x143d+j) (by
        have hn : 0x1442 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
  have hne : (Update.Counter.incM64Effect (pc kind 0x704) am s).rip ≠ boundary.rip := by
    rcases hk with rfl | rfl | rfl
    · exact text_address_ne_return hout 0x709 (by decide +kernel)
    · exact text_address_ne_return hout 0xdb9 (by decide +kernel)
    · exact text_address_ne_return hout 0x1442 (by decide +kernel)
  obtain ⟨u, hau, hru, he⟩ := hs.advances hr hb hp hne
  have hcomponents : (Update.Counter.incM64Effect (pc kind 0x704) am s).components =
      [.mem (stackPtr s + stackOffset kind 88) 8, .flags, .rip] := by
    rcases hk with rfl | rfl | rfl <;> x86_norm [am, stackOffset, UpdateKind.contextOffset, stackPtr]
    all_goals rfl
  have hcu : CodeIn Extracted.programImage u := by
    apply CodeIn.of_agreesExcept he.agrees _ hc
    intro x hx c hm hcover
    rw [hcomponents] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · obtain ⟨i, hi, heq⟩ := hcover
      exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
    · exact hcover
    · exact hcover
  have huip : u.RIP = pc kind 0x709 := by
    rw [he.rip]
    rcases hk with rfl | rfl | rfl <;> rfl
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    partial_compress_prepare_of_kind hk boundary hout u hru hcu huip
  refine ⟨1 + ft, t, hau.trans hat, hrt, hct, ?_⟩
  have hall : ∀ w ∈ (Update.Counter.incM64Effect (pc kind 0x704) am s).writes, w.Full := by
    simp [Update.Counter.incM64Effect, Write.Full, Operand.Full]
  have hseq := he.seq (partialCompressEffect_local_of_kind kind) hall hf
  apply hseq.weaken
  · rcases hk with rfl | rfl | rfl <;> x86_norm [incrementPrepareEffect_of_kind, am, pc]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [incrementPrepareEffect_of_kind, am, stackPtr, stackOffset, UpdateKind.contextOffset]
    all_goals exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  · rcases hk with rfl | rfl | rfl <;> intro i <;> cases i <;> x86_norm [incrementPrepareEffect_of_kind, am]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [incrementPrepareEffect_of_kind, am, stackPtr, stackOffset, UpdateKind.contextOffset]
    all_goals rfl

attribute [local x86_compose] partialCompressEffect

theorem partialCompressEffect_local : Effect.Local partialCompressEffect := by
  exact partialCompressEffect_local_of_kind .resetFirst

def incrementPrepareBytes : List UInt8 :=
  [0x48, 0xff, 0x44, 0x24, 0x58] ++ partialCompressBytes

def incrementPrepareEffect (s : RamState) : Effect :=
  { rip := 0x100718
    writes := [⟨(.mem (stackPtr s + 88) : Operand 64),
      (.mem (stackPtr s + 88) : Operand 64).read s + 1⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 8⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem increment_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100704 ∧
      Memory.MemWritable s (stackPtr s + 88) 8 ∧
      RangeApart (stackPtr s + 88) 8 0x100704 20)
      (codeRange 0x100704 incrementPrepareBytes) incrementPrepareEffect := by
  have hfirst := AdvancesBlock.first
    (Update.Counter.inc_m64_effect_step 0x100704 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide))
    (codeRange_mem_of_drop (p := 0x100704) 0 (by decide +kernel))
    (P := fun s ↦ s.RIP = 0x100704 ∧ Memory.MemWritable s (stackPtr s + 88) 8 ∧
      RangeApart (stackPtr s + 88) 8 0x100704 20)
    (code := codeRange 0x100704 incrementPrepareBytes)
    (fun s h ↦ by
      refine ⟨h.1, ?_, ?_⟩
      · x86_norm
        exact h.2.1
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right h.2.2 0 5 (by decide))
    (fun s h ↦ by
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ h.2.2 rfl
      intro c hc hm
      have heq : (Update.Counter.incM64Effect 0x100704
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [heq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm)
    (fun _ _ ↦ text_address_ne_return hOutside 0x709 (by decide +kernel))
  have hnext := hfirst.seq_block (partial_compress_prepare boundary hOutside)
    partialCompressEffect_local
    (codeRange_mem_of_drop (p := 0x100704) 5 (by decide +kernel))
    (by intro s _; simp [Update.Counter.incM64Effect, Write.Full, Operand.Full])
    (by intro s t _ he _; exact ⟨he.rip,
      Effect.Avoids.of_noMem (by simp [partialCompressEffect, Effect.components, Component.Covers]) _⟩)
  refine AdvancesBlock.block_end ?_ hnext
  intro s t _ he
  apply he.weaken
  · x86_norm [incrementPrepareEffect]
  · x86_norm [incrementPrepareEffect, stackPtr]
    exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [incrementPrepareEffect]
  · x86_norm [incrementPrepareEffect, stackPtr]
    rfl

end Md5.Proofs.Buffered.ResetFirst
