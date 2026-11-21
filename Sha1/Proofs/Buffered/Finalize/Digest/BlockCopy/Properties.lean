import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Clear
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.FinalA
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.FinalB
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Length
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.LongA
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.LongB
import Sha1.Proofs.Buffered.Finalize.Digest.Prepare

namespace Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

theorem longA_avoids {s : RamState} (h : Storage .digestCopy s) :
    (longAEffect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [longAEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 176) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 168) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 160) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 152) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem longA_rsp {s t : RamState} (h : (longAEffect s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [longAEffect, Effect.components]

theorem longA_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x10013c s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (longAEffect s).Holds s t := by
  have hb : CodeIn (codeRange 0x10013c longABytes) s :=
    program_text_slice hc 0x13c 52 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := longA_execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (longA_avoids h.toStorage) hc, he⟩

theorem longA_byte {s t : RamState} (h : (longAEffect s).Holds s t) (j : Nat) (hj : j < 280)
    (hapart : (176 + 8 ≤ j ∨ j + 1 ≤ 176) ∧ (168 + 8 ≤ j ∨ j + 1 ≤ 168) ∧ (160 + 8 ≤ j ∨ j + 1 ≤ 160) ∧ (152 + 8 ≤ j ∨ j + 1 ≤ 152)) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply h.agrees.byte
  intro c hc hcov
  simp only [longAEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact covers_apart (base := stackPtr s) (a := 176) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 168) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 160) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 152) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2 hcov

theorem longB_avoids {s : RamState} (h : Storage .digestCopy s) :
    (longBEffect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [longBEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 144) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 136) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 128) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 120) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem longB_rsp {s t : RamState} (h : (longBEffect s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [longBEffect, Effect.components]

theorem longB_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x100170 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (longBEffect s).Holds s t := by
  have hb : CodeIn (codeRange 0x100170 longBBytes) s :=
    program_text_slice hc 0x170 49 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := longB_execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (longB_avoids h.toStorage) hc, he⟩

theorem longB_byte {s t : RamState} (h : (longBEffect s).Holds s t) (j : Nat) (hj : j < 280)
    (hapart : (144 + 8 ≤ j ∨ j + 1 ≤ 144) ∧ (136 + 8 ≤ j ∨ j + 1 ≤ 136) ∧ (128 + 8 ≤ j ∨ j + 1 ≤ 128) ∧ (120 + 8 ≤ j ∨ j + 1 ≤ 120)) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply h.agrees.byte
  intro c hc hcov
  simp only [longBEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact covers_apart (base := stackPtr s) (a := 144) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 136) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 128) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 120) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2 hcov

theorem finalA_avoids {s : RamState} (h : Storage .digestCopy s) :
    (finalAEffect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [finalAEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 168) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 160) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 152) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem finalA_rsp {s t : RamState} (h : (finalAEffect s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [finalAEffect, Effect.components]

theorem finalA_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x10020d s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (finalAEffect s).Holds s t := by
  have hb : CodeIn (codeRange 0x10020d finalABytes) s :=
    program_text_slice hc 0x20d 39 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := finalA_execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (finalA_avoids h.toStorage) hc, he⟩

theorem finalA_byte {s t : RamState} (h : (finalAEffect s).Holds s t) (j : Nat) (hj : j < 280)
    (hapart : (168 + 8 ≤ j ∨ j + 1 ≤ 168) ∧ (160 + 8 ≤ j ∨ j + 1 ≤ 160) ∧ (152 + 8 ≤ j ∨ j + 1 ≤ 152)) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply h.agrees.byte
  intro c hc hcov
  simp only [finalAEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact covers_apart (base := stackPtr s) (a := 168) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 160) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 152) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2 hcov

theorem finalB_avoids {s : RamState} (h : Storage .digestCopy s) :
    (finalBEffect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [finalBEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 144) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 136) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 128) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 120) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem finalB_rsp {s t : RamState} (h : (finalBEffect s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [finalBEffect, Effect.components]

theorem finalB_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x100234 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (finalBEffect s).Holds s t := by
  have hb : CodeIn (codeRange 0x100234 finalBBytes) s :=
    program_text_slice hc 0x234 49 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := finalB_execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (finalB_avoids h.toStorage) hc, he⟩

theorem finalB_byte {s t : RamState} (h : (finalBEffect s).Holds s t) (j : Nat) (hj : j < 280)
    (hapart : (144 + 8 ≤ j ∨ j + 1 ≤ 144) ∧ (136 + 8 ≤ j ∨ j + 1 ≤ 136) ∧ (128 + 8 ≤ j ∨ j + 1 ≤ 128) ∧ (120 + 8 ≤ j ∨ j + 1 ≤ 120)) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply h.agrees.byte
  intro c hc hcov
  simp only [finalBEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact covers_apart (base := stackPtr s) (a := 144) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 136) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 128) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 120) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2 hcov

theorem clear_avoids {s : RamState} (h : Storage .digestCopy s) :
    (clearEffect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [clearEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 24) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 32) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 40) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 48) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 56) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 64) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 72) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem clear_rsp {s t : RamState} (h : (clearEffect s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [clearEffect, Effect.components]

theorem clear_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x1001b3 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (clearEffect s).Holds s t := by
  have hb : CodeIn (codeRange 0x1001b3 clearBytes) s :=
    program_text_slice hc 0x1b3 63 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := clear_execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (clear_avoids h.toStorage) hc, he⟩

theorem clear_byte {s t : RamState} (h : (clearEffect s).Holds s t) (j : Nat) (hj : j < 280)
    (hapart : (24 + 8 ≤ j ∨ j + 1 ≤ 24) ∧ (32 + 8 ≤ j ∨ j + 1 ≤ 32) ∧ (40 + 8 ≤ j ∨ j + 1 ≤ 40) ∧ (48 + 8 ≤ j ∨ j + 1 ≤ 48) ∧ (56 + 8 ≤ j ∨ j + 1 ≤ 56) ∧ (64 + 8 ≤ j ∨ j + 1 ≤ 64) ∧ (72 + 8 ≤ j ∨ j + 1 ≤ 72)) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply h.agrees.byte
  intro c hc hcov
  simp only [clearEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact covers_apart (base := stackPtr s) (a := 24) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 32) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 40) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 48) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 56) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 64) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2.2.2.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 72) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2.2.2.2.2.2 hcov

theorem length_avoids {s : RamState} (h : Storage .digestCopy s) :
    (lengthEffect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 80) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 176) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem length_rsp {s t : RamState} (h : (lengthEffect s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [lengthEffect, Effect.components]

theorem length_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x1001f2 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (lengthEffect s).Holds s t := by
  have hb : CodeIn (codeRange 0x1001f2 lengthBytes) s :=
    program_text_slice hc 0x1f2 27 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := length_execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (length_avoids h.toStorage) hc, he⟩

theorem length_byte {s t : RamState} (h : (lengthEffect s).Holds s t) (j : Nat) (hj : j < 280)
    (hapart : (80 + 8 ≤ j ∨ j + 1 ≤ 80) ∧ (176 + 8 ≤ j ∨ j + 1 ≤ 176)) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply h.agrees.byte
  intro c hc hcov
  simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact covers_apart (base := stackPtr s) (a := 80) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.1 hcov
  · exact covers_apart (base := stackPtr s) (a := 176) (len := 8) (b := j) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) hapart.2 hcov

end Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy
