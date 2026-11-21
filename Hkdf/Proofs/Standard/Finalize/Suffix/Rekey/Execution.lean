import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Frame
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Stages
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Compression

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Program Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.StreamPadding (base regions)
open Hkdf.Proofs.Common.StreamPadding.Execution

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}

omit [Bindings] in
private theorem setup_offset (outer : Bool) (offset : Nat)
    (member : offset ∈ Stages.setupOffsets outer) :
    ((8 ≤ offset ∧ offset + 8 ≤ 136) ∨ (248 ≤ offset ∧ offset + 8 ≤ 368)) ∧
      offset % 8 = 0 := by
  cases outer <;>
    simp only [Stages.setupOffsets, Bool.false_eq_true, ite_false, ite_true,
      List.mem_cons, List.not_mem_nil, or_false] at member <;> omega

private theorem setup_pre (outer : Bool)
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = Stages.setupStart outer) :
    Stages.SetupPre outer s := by
  have span : ∀ i, i < (Stages.setupBytes outer).length →
      InProgram (Stages.setupStart outer + BitVec.ofNat 64 i) := by
    intro i hi
    cases outer
    · change InProgram (Extracted.textAddress + BitVec.ofNat 64 0xe0ee + BitVec.ofNat 64 i)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset _ (by change i < 102 at hi; omega)
    · change InProgram (Extracted.textAddress + BitVec.ofNat 64 0xe17e + BitVec.ofNat 64 i)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset _ (by change i < 44 at hi; omega)
  refine ⟨rip, ?_, ?_⟩
  · intro offset member
    have bounds := setup_offset outer offset member
    exact local_writable8 .hmac pre state.running state.rsp offset
      (by simp only [Common.StreamPadding.Variant.frame]; omega) bounds.2
  · intro offset member
    have bounds := setup_offset outer offset member
    exact local_codeApart .hmac pre state.rsp offset 8 (Stages.setupStart outer)
      (Stages.setupBytes outer).length
      (by simp only [Common.StreamPadding.Variant.frame]; omega) span

private theorem setup_footprint (outer : Bool)
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) :
    WritesWithin (Stages.setupEffect outer s).components (writes initial) := by
  intro c member a covered
  cases outer <;>
    simp only [Stages.setupEffect, Bool.false_eq_true, ite_false, ite_true,
      Effect.components, List.map_append, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
  · rcases member with ((rfl | rfl | rfl | rfl) |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals exact local_within pre state.rsp _ 8 (by right; constructor <;> decide) a covered
  · rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals exact local_within pre state.rsp _ 8 (by left; constructor <;> decide) a covered

theorem setup (outer : Bool)
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = Stages.setupStart outer) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = Stages.setupEnd outer ∧
      t.regValue .rdi = stackPtr t + (if outer then 8 else 248) ∧
      t.regValue .rsi = stackPtr t + 72 ∧ t.regValue .rdx = 1 ∧
      MemoryWriteFrame s t (writes initial) ∧ (Stages.setupEffect outer s).Holds s t := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Stages.setup_run outer boundary pre.outerBoundary
    s (supportedMachine_readyToStep state.running.machine) (Stages.setup_code outer state.running.loaded)
      (setup_pre outer pre state rip)
  have within := setup_footprint outer pre state
  have frame := effect.agrees.memoryWriteFrame within
  have kept : ∀ c ∈ ([.reg 4, .reg 3, .reg 5, .mxcsr, .fcw, .df] : List Component),
      c ∉ (Stages.setupEffect outer s).components := by
    cases outer <;> simp [Stages.setupEffect, Effect.components, Write.component, Operand.component]
  have final := state.of_agrees pre run ready effect.agrees (by
    intro c hc a ha
    obtain ⟨region, member, contains⟩ := within c hc a ha
    exact writes_within pre region member a.toNat contains) kept (saved_after pre frame)
  have rsp : stackPtr t = stackPtr s :=
    effect.agrees.read (n := 64) (r := 4) (kept _ (by simp))
  obtain ⟨destination, source, count⟩ := Stages.setup_arguments outer effect
  exact ⟨t, final, effect.rip, by simpa only [rsp] using destination,
    by simpa only [rsp] using source, count, frame, effect⟩

theorem compress {block : ByteArray} {hash : Array UInt32} (outer : Bool)
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s)
    (rip : s.RIP = if outer then 0x10e1aa else 0x10e154)
    (destination : s.regValue .rdi = stackPtr s + (if outer then 8 else 248))
    (source : s.regValue .rsi = stackPtr s + 72) (count : s.regValue .rdx = 1)
    (bytes : (MemoryRegion.mk (stackPtr s + 72).toNat 64).HasBytes s.external block)
    (words : Common.SHA256.HashStateAt s
      (stackPtr s + BitVec.ofNat 64 (Compression.hashOffset outer)) hash) :
    ∃ t, Suffix.State initial boundary t ∧
      t.RIP = (if outer then 0x10e1af else 0x10e159) ∧
      MemoryWriteFrame s t (writes initial) ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[
        MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 (Compression.hashOffset outer)).toNat 32,
        MemoryRegion.mk (stackPtr s - 344).toNat 344] ∧
      Common.SHA256.HashStateAt t (stackPtr s + BitVec.ofNat 64 (Compression.hashOffset outer))
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) := by
  obtain ⟨fuel, t, run, ready, running, ripT, rspT, abi, memory, wordsT⟩ := Compression.run outer pre
    state.running state.rsp rip destination source count bytes words
  change MemoryWriteFrame s t #v[
    MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 (if outer then 8 else 248)).toNat 32,
    MemoryRegion.mk (stackPtr s - 344).toNat 344] at memory
  have sp : stackPtr s = base .hmac initial := state.rsp
  have frame : MemoryWriteFrame s t (writes initial) := by
    apply frame_mono memory
    intro region member a contains
    have cases : region = ⟨(stackPtr s + BitVec.ofNat 64 (if outer then 8 else 248)).toNat, 32⟩ ∨
        region = ⟨(stackPtr s - 344).toNat, 344⟩ := by
      cases outer <;> simpa using member
    rcases cases with rfl | rfl
    · cases outer
      · refine ⟨⟨(base .hmac initial + 248).toNat, 120⟩, by simp [writes], ?_⟩
        change (base .hmac initial + 248).toNat ≤ a ∧
          a < (base .hmac initial + 248).toNat + 120
        change (stackPtr s + 248).toNat ≤ a ∧ a < (stackPtr s + 248).toNat + 32 at contains
        rw [sp] at contains
        exact ⟨contains.1, by omega⟩
      · refine ⟨⟨(base .hmac initial + 8).toNat, 128⟩, by simp [writes], ?_⟩
        change (base .hmac initial + 8).toNat ≤ a ∧
          a < (base .hmac initial + 8).toNat + 128
        change (stackPtr s + 8).toNat ≤ a ∧ a < (stackPtr s + 8).toNat + 32 at contains
        rw [sp] at contains
        exact ⟨contains.1, by omega⟩
    · refine ⟨⟨(base .hmac initial - 344).toNat, 344⟩, by simp [writes], ?_⟩
      simpa only [sp] using contains
  exact ⟨t, state.of_running running abi rspT (saved_after pre frame),
    ripT, frame, abi, memory, wordsT⟩

private theorem copy_pre
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e1af) : Stages.CopyPre s := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    exact local_readable .hmac pre state.running state.rsp offset 8
      (by simp only [Common.StreamPadding.Variant.frame]; omega)
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    exact local_writable8 .hmac pre state.running state.rsp offset
      (by simp only [Common.StreamPadding.Variant.frame]; omega) (by omega)
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    apply local_codeApart .hmac pre state.rsp offset 8 0x10e1af Stages.copyBytes.length
      (by simp only [Common.StreamPadding.Variant.frame]; omega)
    intro i hi
    change InProgram (Extracted.textAddress + BitVec.ofNat 64 0xe1af + BitVec.ofNat 64 i)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by change i < 145 at hi; omega)

private theorem copy_footprint
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) :
    WritesWithin (Stages.copyEffect s).components (writes initial) := by
  intro c member a covered
  simp only [Stages.copyEffect, Effect.components, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals exact local_within pre state.rsp _ 8 (by right; constructor <;> decide) a covered

theorem copy
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e1af) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e240 ∧
      MemoryWriteFrame s t (writes initial) ∧ (Stages.copyEffect s).Holds s t := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Stages.copy_run boundary pre.outerBoundary
    s (supportedMachine_readyToStep state.running.machine) (Stages.copy_code state.running.loaded)
      (copy_pre pre state rip)
  have within := copy_footprint pre state
  have frame := effect.agrees.memoryWriteFrame within
  have final := state.of_agrees pre run ready effect.agrees (by
    intro c hc a ha
    obtain ⟨region, member, contains⟩ := within c hc a ha
    exact writes_within pre region member a.toNat contains)
    (by simp [Stages.copyEffect, Effect.components, Write.component, Operand.component])
    (saved_after pre frame)
  exact ⟨t, final, effect.rip, frame, effect⟩

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey
