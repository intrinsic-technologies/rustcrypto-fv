import P256.Proofs.Verifying.Combination.Naf.Iterator.InitializeRead
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Common.Instructions (RangeApart.add_left)

structure InitializeStorePre (s : RamState) : Prop where
  rip : s.RIP = 0x1182c5
  output : Writable s (s.regValue .rbx) 40
  apart : RangeApart (s.regValue .rbx) 40 0x1182c5 26

def initializeStoreBytes : List UInt8 :=
  [0x48,0x89,0x33,0x48,0x89,0x53,0x08,0x48,0xc7,0x43,0x10,0,0,0,0,
   0x4c,0x89,0x73,0x18,0x48,0x89,0x4b,0x20,0x48,0x89,0xd8]

def initializeStoreEffect (s : RamState) : Effect :=
  { rip := 0x1182df
    writes := [⟨(Operand.mem (s.regValue .rbx) : Operand 64), s.regValue .rsi⟩,
      ⟨(Operand.mem (s.regValue .rbx + 8) : Operand 64), s.regValue .rdx⟩,
      ⟨(Operand.mem (s.regValue .rbx + 16) : Operand 64), 0⟩,
      ⟨(Operand.mem (s.regValue .rbx + 24) : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.mem (s.regValue .rbx + 32) : Operand 64), s.regValue .rcx⟩,
      ⟨(Operand.reg 0 : Operand 64), s.regValue .rbx⟩] }

theorem slot_read {s t : RamState} {base written kept : BitVec 64}
    (h : AgreesExcept [.mem (base + written) 8, .rip] s t)
    (apart : OffsetsApart written 8 kept 8) :
    memLoad t.external (base + kept) 64 = memLoad s.external (base + kept) 64 := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := cover
    exact apart.ne base hj hi (by decide) he.symm
  · exact cover.elim

theorem writable_grow {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : Writable s addr len)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    Writable t addr len := ⟨⟨h.low, fun i hi => grow _ (h.mem i hi)⟩, h.tables⟩

theorem initialize_store [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InitializeStorePre (codeRange 0x1182c5 initializeStoreBytes)
      (Effect.post initializeStoreEffect) := by
  intro s ready code pre
  have w1 : Writable s (s.regValue .rbx + 0#64) 8 :=
    pre.output.add 0 (by decide)
  have apart1 : RangeApart (s.regValue .rbx + 0#64) 8 0x1182c5 3 := by
    intro i hi j hj he
    apply pre.apart (0 + i) (by omega) (0 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using he
  obtain ⟨s1, run1, ready1, raw1⟩ :=
    (mov_m64_r64_effect_step_any 0x1182c5 0x48 (by simp [RexWPrefix]) 6 (.base 3 .none) (by decide +kernel) rfl rfl).advances ready
      (code.mono (codeRange_slice_subset 0x1182c5 initializeStoreBytes 0 3))
      ⟨pre.rip, by
        change Writable s (s.regValue .rbx + 0#64) 8
        exact w1
      , by
        change RangeApart (s.regValue .rbx + 0#64) 8 0x1182c5 3
        exact apart1⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x182c8 (by decide)))
  have e1 : ({ rip := 0x1182c8, writes := [⟨(Operand.mem (s.regValue .rbx + 0#64) : Operand 64), s.regValue .rsi⟩] } : Effect).Holds s s1 := by
    change ({ rip := 0x1182c8, writes := [⟨(Operand.mem (s.regValue .rbx + 0#64) : Operand 64), s.regValue .rsi⟩] } : Effect).Holds s s1 at raw1
    exact raw1
  have a1 : AgreesExcept [.mem (s.regValue .rbx + 0#64) 8, .rip] s s1 := by simpa [Effect.components] using e1.agrees
  have ag1 := a1
  have code1 := e1.codeIn (by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := pre.apart) 0 (by decide)
    · cases he) code
  have b2 : s1.regValue .rbx = s.regValue .rbx := ag1.read (n := 64) (r := 3) (by simp)
  have w2 : Writable s1 (s.regValue .rbx + 8#64) 8 :=
    writable_grow (pre.output.add 8 (by decide)) ag1.grow
  have apart2 : RangeApart (s.regValue .rbx + 8#64) 8 0x1182c8 4 := by
    intro i hi j hj he
    apply pre.apart (8 + i) (by omega) (3 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using he
  obtain ⟨s2, run2, ready2, raw2⟩ :=
    (mov_m64_r64_effect_step_any 0x1182c8 0x48 (by simp [RexWPrefix]) 2 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl).advances ready1
      (code1.mono (codeRange_slice_subset 0x1182c5 initializeStoreBytes 3 4))
      ⟨e1.rip, by
        change Writable s1 (s1.regValue .rbx + 8#64) 8
        rw [b2]; exact w2
      , by
        change RangeApart (s1.regValue .rbx + 8#64) 8 0x1182c8 4
        rw [b2]; exact apart2⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x182cc (by decide)))
  have v2 : s1.regValue .rdx = s.regValue .rdx := ag1.read (n := 64) (r := 2) (by simp)
  have e2 : ({ rip := 0x1182cc, writes := [⟨(Operand.mem (s.regValue .rbx + 8#64) : Operand 64), s.regValue .rdx⟩] } : Effect).Holds s1 s2 := by
    change ({ rip := 0x1182cc, writes := [⟨(Operand.mem (s1.regValue .rbx + 8#64) : Operand 64), s1.regValue .rdx⟩] } : Effect).Holds s1 s2 at raw2
    simpa only [b2, v2] using raw2
  have a2 : AgreesExcept [.mem (s.regValue .rbx + 8#64) 8, .rip] s1 s2 := by simpa [Effect.components] using e2.agrees
  have ag2 := ag1.trans a2
  have code2 := e2.codeIn (by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := pre.apart) 8 (by decide)
    · cases he) code1
  have b3 : s2.regValue .rbx = s.regValue .rbx := ag2.read (n := 64) (r := 3) (by simp)
  have w3 : Writable s2 (s.regValue .rbx + 16#64) 8 :=
    writable_grow (pre.output.add 16 (by decide)) ag2.grow
  have apart3 : RangeApart (s.regValue .rbx + 16#64) 8 0x1182cc 8 := by
    intro i hi j hj he
    apply pre.apart (16 + i) (by omega) (7 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using he
  obtain ⟨s3, run3, ready3, raw3⟩ :=
    (mov_m64_imm32_effect_step_any 0x1182cc 0x48 (by simp [RexWPrefix]) (.base 3 (.d8 16)) (by decide +kernel) rfl rfl 0).advances ready2
      (code2.mono (codeRange_slice_subset 0x1182c5 initializeStoreBytes 7 8))
      ⟨e2.rip, by
        change Writable s2 (s2.regValue .rbx + 16#64) 8
        rw [b3]; exact w3
      , by
        change RangeApart (s2.regValue .rbx + 16#64) 8 0x1182cc 8
        rw [b3]; exact apart3⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x182d4 (by decide)))
  have e3 : ({ rip := 0x1182d4, writes := [⟨(Operand.mem (s.regValue .rbx + 16#64) : Operand 64), 0#64⟩] } : Effect).Holds s2 s3 := by
    change ({ rip := 0x1182d4, writes := [⟨(Operand.mem (s2.regValue .rbx + 16#64) : Operand 64), 0#64⟩] } : Effect).Holds s2 s3 at raw3
    simpa only [b3] using raw3
  have a3 : AgreesExcept [.mem (s.regValue .rbx + 16#64) 8, .rip] s2 s3 := by simpa [Effect.components] using e3.agrees
  have ag3 := ag2.trans a3
  have code3 := e3.codeIn (by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := pre.apart) 16 (by decide)
    · cases he) code2
  have b4 : s3.regValue .rbx = s.regValue .rbx := ag3.read (n := 64) (r := 3) (by simp)
  have w4 : Writable s3 (s.regValue .rbx + 24#64) 8 :=
    writable_grow (pre.output.add 24 (by decide)) ag3.grow
  have apart4 : RangeApart (s.regValue .rbx + 24#64) 8 0x1182d4 4 := by
    intro i hi j hj he
    apply pre.apart (24 + i) (by omega) (15 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using he
  obtain ⟨s4, run4, ready4, raw4⟩ :=
    (mov_m64_r64_effect_step_any 0x1182d4 0x4c (by simp [RexWPrefix]) 6 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl).advances ready3
      (code3.mono (codeRange_slice_subset 0x1182c5 initializeStoreBytes 15 4))
      ⟨e3.rip, by
        change Writable s3 (s3.regValue .rbx + 24#64) 8
        rw [b4]; exact w4
      , by
        change RangeApart (s3.regValue .rbx + 24#64) 8 0x1182d4 4
        rw [b4]; exact apart4⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x182d8 (by decide)))
  have v4 : s3.regValue .r14 = s.regValue .r14 := ag3.read (n := 64) (r := 14) (by simp)
  have e4 : ({ rip := 0x1182d8, writes := [⟨(Operand.mem (s.regValue .rbx + 24#64) : Operand 64), s.regValue .r14⟩] } : Effect).Holds s3 s4 := by
    change ({ rip := 0x1182d8, writes := [⟨(Operand.mem (s3.regValue .rbx + 24#64) : Operand 64), s3.regValue .r14⟩] } : Effect).Holds s3 s4 at raw4
    simpa only [b4, v4] using raw4
  have a4 : AgreesExcept [.mem (s.regValue .rbx + 24#64) 8, .rip] s3 s4 := by simpa [Effect.components] using e4.agrees
  have ag4 := ag3.trans a4
  have code4 := e4.codeIn (by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := pre.apart) 24 (by decide)
    · cases he) code3
  have b5 : s4.regValue .rbx = s.regValue .rbx := ag4.read (n := 64) (r := 3) (by simp)
  have w5 : Writable s4 (s.regValue .rbx + 32#64) 8 :=
    writable_grow (pre.output.add 32 (by decide)) ag4.grow
  have apart5 : RangeApart (s.regValue .rbx + 32#64) 8 0x1182d8 4 := by
    intro i hi j hj he
    apply pre.apart (32 + i) (by omega) (19 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using he
  obtain ⟨s5, run5, ready5, raw5⟩ :=
    (mov_m64_r64_effect_step_any 0x1182d8 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl).advances ready4
      (code4.mono (codeRange_slice_subset 0x1182c5 initializeStoreBytes 19 4))
      ⟨e4.rip, by
        change Writable s4 (s4.regValue .rbx + 32#64) 8
        rw [b5]; exact w5
      , by
        change RangeApart (s4.regValue .rbx + 32#64) 8 0x1182d8 4
        rw [b5]; exact apart5⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x182dc (by decide)))
  have v5 : s4.regValue .rcx = s.regValue .rcx := ag4.read (n := 64) (r := 1) (by simp)
  have e5 : ({ rip := 0x1182dc, writes := [⟨(Operand.mem (s.regValue .rbx + 32#64) : Operand 64), s.regValue .rcx⟩] } : Effect).Holds s4 s5 := by
    change ({ rip := 0x1182dc, writes := [⟨(Operand.mem (s4.regValue .rbx + 32#64) : Operand 64), s4.regValue .rcx⟩] } : Effect).Holds s4 s5 at raw5
    simpa only [b5, v5] using raw5
  have a5 : AgreesExcept [.mem (s.regValue .rbx + 32#64) 8, .rip] s4 s5 := by simpa [Effect.components] using e5.agrees
  have ag5 := ag4.trans a5
  have code5 := e5.codeIn (by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := pre.apart) 32 (by decide)
    · cases he) code4
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (mov_r64_r64_effect_step 0x1182dc 0x48 0xd8 (by simp [RexWPrefix]) rfl).advances ready5
      (code5.mono (codeRange_slice_subset 0x1182c5 initializeStoreBytes 23 3)) e5.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x182df (by decide)))
  change (movR64R64Effect 0x1182dc 0 3 s5).Holds s5 s6 at e6
  have code6 := e6.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code5
  have mem6 := e6.agrees.external (by simp [Component.Covers])
  refine ⟨6, s6, ((((run1.trans run2).trans run3).trans run4).trans run5).trans run6,
    ready6, code6, e6.rip, ?_, trivial, ?_⟩
  · change memLoad s6.external (s.regValue .rbx) 64 = s.regValue .rsi ∧
      memLoad s6.external (s.regValue .rbx + 8#64) 64 = s.regValue .rdx ∧
      memLoad s6.external (s.regValue .rbx + 16#64) 64 = 0#64 ∧
      memLoad s6.external (s.regValue .rbx + 24#64) 64 = s.regValue .r14 ∧
      memLoad s6.external (s.regValue .rbx + 32#64) 64 = s.regValue .rcx ∧
      s6.regValue .rax = s.regValue .rbx
    rw [mem6]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← BitVec.add_zero (s.regValue .rbx)]
      rw [slot_read a5 (by unfold OffsetsApart; decide +kernel), slot_read a4 (by unfold OffsetsApart; decide +kernel), slot_read a3 (by unfold OffsetsApart; decide +kernel), slot_read a2 (by unfold OffsetsApart; decide +kernel)]
      exact e1.writes
    · rw [slot_read a5 (by unfold OffsetsApart; decide +kernel), slot_read a4 (by unfold OffsetsApart; decide +kernel), slot_read a3 (by unfold OffsetsApart; decide +kernel)]
      exact e2.writes
    · rw [slot_read a5 (by unfold OffsetsApart; decide +kernel), slot_read a4 (by unfold OffsetsApart; decide +kernel)]
      exact e3.writes
    · rw [slot_read a5 (by unfold OffsetsApart; decide +kernel)]
      exact e4.writes
    · exact e5.writes
    · exact e6.writes.trans (ag5.read (n := 64) (r := 3) (by simp))
  · apply (ag5.trans e6.agrees).mono
    simp [initializeStoreEffect, movR64R64Effect, Effect.components]

end P256.Proofs.Verifying.Combination.Naf.Iterator
