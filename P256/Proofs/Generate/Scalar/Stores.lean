import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StoreLimbsPre (s : RamState) : Prop where
  rip : s.RIP = 0x112fab
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def storeLimbsBytes : List UInt8 :=
  [0x4c,0x89,0x2b,0x4c,0x89,0x63,0x08,0x4c,0x89,0x7b,0x10,0x4c,0x89,0x73,0x18]

def storeLimbsEffect (s : RamState) : Effect :=
  { rip := 0x112fba
    writes := [
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 0) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

theorem store_limbs_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StoreLimbsPre (codeRange 0x112fab storeLimbsBytes)
      (Effect.post storeLimbsEffect) := by
  intro s ready code pre
  let dst := (Operand.reg 3 : Operand 64).read s
  have pre1 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x112fab 3
      (fun t => (AddrMode.base 3 .none).addr t 0x112fae) 8 s := by
    refine ⟨pre.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + 0) 8
      exact pre.writable 0 (by simp)
    · change RangeApart ((Operand.reg 3 : Operand 64).read s + 0) 8 0x112fab 3
      exact pre.codeApart 0 (by simp) 0x12fab 3 (by decide)
  obtain ⟨s1, e1, ready1, h1⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112fab 0x4c
      (by unfold RexWPrefix; decide +kernel) 5 (.base 3 .none) (by decide +kernel) rfl rfl).advances ready
      (code.mono (codeRange_slice_subset 0x112fab storeLimbsBytes 0 3)) pre1
      (boundary_ne_program hout (inProgram_of_textOffset 0x12fae (by decide)))
  change ({rip := 0x112fae, writes :=
    [⟨(Operand.mem ((Operand.reg 3 : Operand 64).read s + 0) : Operand 64),
      (Operand.reg 13 : Operand 64).read s⟩]} : Effect).Holds s s1 at h1
  have f1 : AgreesExcept [.mem (dst + 0) 8, .rip] s s1 := by simpa [Effect.components, dst] using h1.agrees
  have fAll1 := f1
  have g1 (r : BitVec 5) : (Operand.reg r : Operand 64).read s1 =
      (Operand.reg r : Operand 64).read s := fAll1.read (by simp)
  have av1 : ({rip := 0x112fae, writes :=
      [⟨(Operand.mem (dst + 0) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange 0x112fab storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 0 (by simp) 0x12fab 15 (by decide)
    · cases he
  have code1 := h1.codeIn av1 code
  have pre2 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x112fae 4
      (fun t => (AddrMode.base 3 (.d8 8)).addr t 0x112fb2) 8 s1 := by
    refine ⟨h1.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s1 ((Operand.reg 3 : Operand 64).read s1 + 8) 8
      rw [g1]
      exact (pre.writable 8 (by simp)).of_holds h1
    · change RangeApart ((Operand.reg 3 : Operand 64).read s1 + 8) 8 0x112fae 4
      rw [g1]
      exact pre.codeApart 8 (by simp) 0x12fae 4 (by decide)
  obtain ⟨s2, e2, ready2, h2⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112fae 0x4c
      (by unfold RexWPrefix; decide +kernel) 4 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl).advances ready1
      (code1.mono (codeRange_slice_subset 0x112fab storeLimbsBytes 3 4)) pre2
      (boundary_ne_program hout (inProgram_of_textOffset 0x12fb2 (by decide)))
  change ({rip := 0x112fb2, writes :=
    [⟨(Operand.mem ((Operand.reg 3 : Operand 64).read s1 + 8) : Operand 64),
      (Operand.reg 12 : Operand 64).read s1⟩]} : Effect).Holds s1 s2 at h2
  rw [g1 3, g1 12] at h2
  have f2 : AgreesExcept [.mem (dst + 8) 8, .rip] s1 s2 := by simpa [Effect.components, dst] using h2.agrees
  have fAll2 := fAll1.trans f2
  have g2 (r : BitVec 5) : (Operand.reg r : Operand 64).read s2 =
      (Operand.reg r : Operand 64).read s := fAll2.read (by simp)
  have av2 : ({rip := 0x112fb2, writes :=
      [⟨(Operand.mem (dst + 8) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange 0x112fab storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 8 (by simp) 0x12fab 15 (by decide)
    · cases he
  have code2 := h2.codeIn av2 code1
  have pre3 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x112fb2 4
      (fun t => (AddrMode.base 3 (.d8 16)).addr t 0x112fb6) 8 s2 := by
    refine ⟨h2.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s2 ((Operand.reg 3 : Operand 64).read s2 + 16) 8
      rw [g2]
      exact ⟨P256.Proofs.Program.readable_of_grow (pre.writable 16 (by simp)).toMemReadable fAll2.grow, (pre.writable 16 (by simp)).tables⟩
    · change RangeApart ((Operand.reg 3 : Operand 64).read s2 + 16) 8 0x112fb2 4
      rw [g2]
      exact pre.codeApart 16 (by simp) 0x12fb2 4 (by decide)
  obtain ⟨s3, e3, ready3, h3⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112fb2 0x4c
      (by unfold RexWPrefix; decide +kernel) 7 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl).advances ready2
      (code2.mono (codeRange_slice_subset 0x112fab storeLimbsBytes 7 4)) pre3
      (boundary_ne_program hout (inProgram_of_textOffset 0x12fb6 (by decide)))
  change ({rip := 0x112fb6, writes :=
    [⟨(Operand.mem ((Operand.reg 3 : Operand 64).read s2 + 16) : Operand 64),
      (Operand.reg 15 : Operand 64).read s2⟩]} : Effect).Holds s2 s3 at h3
  rw [g2 3, g2 15] at h3
  have f3 : AgreesExcept [.mem (dst + 16) 8, .rip] s2 s3 := by simpa [Effect.components, dst] using h3.agrees
  have fAll3 := fAll2.trans f3
  have g3 (r : BitVec 5) : (Operand.reg r : Operand 64).read s3 =
      (Operand.reg r : Operand 64).read s := fAll3.read (by simp)
  have av3 : ({rip := 0x112fb6, writes :=
      [⟨(Operand.mem (dst + 16) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange 0x112fab storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 16 (by simp) 0x12fab 15 (by decide)
    · cases he
  have code3 := h3.codeIn av3 code2
  have pre4 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x112fb6 4
      (fun t => (AddrMode.base 3 (.d8 24)).addr t 0x112fba) 8 s3 := by
    refine ⟨h3.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s3 ((Operand.reg 3 : Operand 64).read s3 + 24) 8
      rw [g3]
      exact ⟨P256.Proofs.Program.readable_of_grow (pre.writable 24 (by simp)).toMemReadable fAll3.grow, (pre.writable 24 (by simp)).tables⟩
    · change RangeApart ((Operand.reg 3 : Operand 64).read s3 + 24) 8 0x112fb6 4
      rw [g3]
      exact pre.codeApart 24 (by simp) 0x12fb6 4 (by decide)
  obtain ⟨s4, e4, ready4, h4⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112fb6 0x4c
      (by unfold RexWPrefix; decide +kernel) 6 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl).advances ready3
      (code3.mono (codeRange_slice_subset 0x112fab storeLimbsBytes 11 4)) pre4
      (boundary_ne_program hout (inProgram_of_textOffset 0x12fba (by decide)))
  change ({rip := 0x112fba, writes :=
    [⟨(Operand.mem ((Operand.reg 3 : Operand 64).read s3 + 24) : Operand 64),
      (Operand.reg 14 : Operand 64).read s3⟩]} : Effect).Holds s3 s4 at h4
  rw [g3 3, g3 14] at h4
  have f4 : AgreesExcept [.mem (dst + 24) 8, .rip] s3 s4 := by simpa [Effect.components, dst] using h4.agrees
  have fAll4 := fAll3.trans f4
  have g4 (r : BitVec 5) : (Operand.reg r : Operand 64).read s4 =
      (Operand.reg r : Operand 64).read s := fAll4.read (by simp)
  have av4 : ({rip := 0x112fba, writes :=
      [⟨(Operand.mem (dst + 24) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange 0x112fab storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 24 (by simp) 0x12fab 15 (by decide)
    · cases he
  have code4 := h4.codeIn av4 code3
  have m21 : (Operand.mem (dst + 0) : Operand 64).read s2 =
      (Operand.mem (dst + 0) : Operand 64).read s1 :=
    P256.Proofs.Program.memLoad_agrees_apart f2 (by
      intro address len hc
      have he : address = dst + 8 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      intro i hi j hj
      exact (show OffsetsApart 8 8 0 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m31 : (Operand.mem (dst + 0) : Operand 64).read s3 =
      (Operand.mem (dst + 0) : Operand 64).read s2 :=
    P256.Proofs.Program.memLoad_agrees_apart f3 (by
      intro address len hc
      have he : address = dst + 16 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      intro i hi j hj
      exact (show OffsetsApart 16 8 0 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m41 : (Operand.mem (dst + 0) : Operand 64).read s4 =
      (Operand.mem (dst + 0) : Operand 64).read s3 :=
    P256.Proofs.Program.memLoad_agrees_apart f4 (by
      intro address len hc
      have he : address = dst + 24 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      intro i hi j hj
      exact (show OffsetsApart 24 8 0 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m32 : (Operand.mem (dst + 8) : Operand 64).read s3 =
      (Operand.mem (dst + 8) : Operand 64).read s2 :=
    P256.Proofs.Program.memLoad_agrees_apart f3 (by
      intro address len hc
      have he : address = dst + 16 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      intro i hi j hj
      exact (show OffsetsApart 16 8 8 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m42 : (Operand.mem (dst + 8) : Operand 64).read s4 =
      (Operand.mem (dst + 8) : Operand 64).read s3 :=
    P256.Proofs.Program.memLoad_agrees_apart f4 (by
      intro address len hc
      have he : address = dst + 24 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      intro i hi j hj
      exact (show OffsetsApart 24 8 8 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m43 : (Operand.mem (dst + 16) : Operand 64).read s4 =
      (Operand.mem (dst + 16) : Operand 64).read s3 :=
    P256.Proofs.Program.memLoad_agrees_apart f4 (by
      intro address len hc
      have he : address = dst + 24 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      intro i hi j hj
      exact (show OffsetsApart 24 8 16 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  refine ⟨4, s4, ((e1.trans e2).trans e3).trans e4, ready4, code4, ?_⟩
  refine ⟨h4.rip, ?_, ?_, ?_⟩
  · change _ ∧ _ ∧ _ ∧ _
    exact ⟨((m41.trans m31).trans m21).trans h1.writes,
      (m42.trans m32).trans h2.writes, m43.trans h3.writes, h4.writes⟩
  · trivial
  · exact fAll4.mono (by simp [storeLimbsEffect, Effect.components, dst])

theorem storeLimbs_bytes :
    Extracted.textBytes.toListFrom 0x12fab storeLimbsBytes.length = storeLimbsBytes := by
  decide +kernel

end P256.Proofs.Generate.Scalar
