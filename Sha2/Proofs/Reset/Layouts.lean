import Sha2.Proofs.Common.SHA256.Instances.Absorb.Chunks
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Code
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Headers
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableLayouts

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program
open X86Proofs
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

private def site (pc : Nat) (block : Blocks.Block) : Blocks.Site :=
  ⟨BitVec.ofNat 64 pc, block⟩

private def resetTable (loop : Loop) (head exit : Nat)
    (nextSmall : List Blocks.Site) (nextLarge : List Blocks.Site) (v : Sha2.Proofs.Wrapper.Variant) : Table.Layout :=
  { chunk := loop.chunk v
    clobbered := [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    index := 15
    count := .reg 12
    pointerSlot := 0xa8
    lengthSlot := 0xb0
    storedOffset := 0
    head := BitVec.ofNat 64 head
    exit := BitVec.ofNat 64 exit
    load := []
    cloneIn := []
    cloneOut := []
    nextSmall := nextSmall
    nextLarge := nextLarge }

def resetDiscarded (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.Layout :=
  { resetTable .resetDiscarded (if v = .sha224 then 0x100df4 else 0x102a24) (if v = .sha224 then 0x100ebb else 0x102aeb)
      [site (if v = .sha224 then 0x100de8 else 0x102a18) (.incrementIndex 15), site (if v = .sha224 then 0x100deb else 0x102a1b) (.compareIndex 15 12),
       site (if v = .sha224 then 0x100dee else 0x102a1e) (.branch 4 (.near 0xc7))]
      [site (if v = .sha224 then 0x100e9f else 0x102acf) (.incrementIndex 15), site (if v = .sha224 then 0x100ea2 else 0x102ad2) (.compareIndex 15 12),
       site (if v = .sha224 then 0x100ea5 else 0x102ad5) (.branch 5 (.near 0xffffff49)), site (if v = .sha224 then 0x100eab else 0x102adb) (.jump (.short 0xe))] v with
    load := [site (if v = .sha224 then 0x100df4 else 0x102a24) (.loadPair 15 14 5 (.d32 0xa8) (.d32 0xb0)),
      site (if v = .sha224 then 0x100e0c else 0x102a3c) (.loadTail 13 (.sib 4 none 0 (.d8 0x3f)))] }

def resetFirst (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.Layout :=
  { resetTable .resetFirst (if v = .sha224 then 0x100f31 else 0x102b61) (if v = .sha224 then 0x100ff6 else 0x102c26)
      [site (if v = .sha224 then 0x100f25 else 0x102b55) (.incrementIndex 15), site (if v = .sha224 then 0x100f28 else 0x102b58) (.compareIndex 15 12),
       site (if v = .sha224 then 0x100f2b else 0x102b5b) (.branch 4 (.near 0xc5))]
      [site (if v = .sha224 then 0x100fda else 0x102c0a) (.incrementIndex 15), site (if v = .sha224 then 0x100fdd else 0x102c0d) (.compareIndex 15 12),
       site (if v = .sha224 then 0x100fe0 else 0x102c10) (.branch 5 (.near 0xffffff4b)), site (if v = .sha224 then 0x100fe6 else 0x102c16) (.jump (.short 0xe))] v with
    load := [site (if v = .sha224 then 0x100f31 else 0x102b61) (.loadPair 15 6 14 (.d32 0xa8) (.d32 0xb0)),
      site (if v = .sha224 then 0x100f49 else 0x102b79) (.loadTail 13 (.sib 4 none 0 (.d8 0x3f)))] }

def resetSecond (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.Layout :=
  { resetTable .resetLast (if v = .sha224 then 0x10123d else 0x102e7d) (if v = .sha224 then 0x1012f6 else 0x102f36)
      [site (if v = .sha224 then 0x101231 else 0x102e71) (.incrementIndex 15), site (if v = .sha224 then 0x101234 else 0x102e74) (.compareIndex 15 12),
       site (if v = .sha224 then 0x101237 else 0x102e77) (.branch 4 (.near 0xb9))]
      [site (if v = .sha224 then 0x1012da else 0x102f1a) (.incrementIndex 15), site (if v = .sha224 then 0x1012dd else 0x102f1d) (.compareIndex 15 12),
       site (if v = .sha224 then 0x1012e0 else 0x102f20) (.branch 5 (.near 0xffffff57)), site (if v = .sha224 then 0x1012e6 else 0x102f26) (.jump (.short 0xe))] v with
    load := [site (if v = .sha224 then 0x10123d else 0x102e7d) (.loadPair 15 6 14 (.d32 0xa8) (.d32 0xb0)),
      site (if v = .sha224 then 0x101255 else 0x102e95) (.loadTail 13 (.sib 4 none 0 (.d8 0x3f)))] }

end Sha2.Proofs.Reset

namespace Sha2.Proofs.Reset

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

theorem resetDiscarded_wellFormed (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.WellFormed (resetDiscarded v) 720 := by
  constructor
  · exact Loop.wellFormed .resetDiscarded v
  all_goals cases v <;> simp [resetDiscarded, resetTable, Loop.chunk, X86Proofs.OffsetsApart]

theorem resetFirst_wellFormed (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.WellFormed (resetFirst v) 720 := by
  constructor
  · exact Loop.wellFormed .resetFirst v
  all_goals cases v <;> simp [resetFirst, resetTable, Loop.chunk, X86Proofs.OffsetsApart]

theorem resetSecond_wellFormed (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.WellFormed (resetSecond v) 720 := by
  constructor
  · exact Loop.wellFormed .resetLast v
  all_goals cases v <;> simp [resetSecond, resetTable, Loop.chunk, X86Proofs.OffsetsApart]

end Sha2.Proofs.Reset

namespace Sha2.Proofs.Reset

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

theorem resetDiscarded_callTargets (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CallTargets (resetDiscarded v).chunk := by
  simpa [resetDiscarded, resetTable] using (Loop.callTargets .resetDiscarded v)

theorem resetFirst_callTargets (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CallTargets (resetFirst v).chunk := by
  simpa [resetFirst, resetTable] using (Loop.callTargets .resetFirst v)

theorem resetSecond_callTargets (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CallTargets (resetSecond v).chunk := by
  simpa [resetSecond, resetTable] using (Loop.callTargets .resetLast v)

end Sha2.Proofs.Reset

namespace Sha2.Proofs.Reset

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

theorem resetDiscarded_flow (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Flow (resetDiscarded v).chunk := by
  simpa [resetDiscarded, resetTable] using (Loop.flow .resetDiscarded v)

theorem resetFirst_flow (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Flow (resetFirst v).chunk := by
  simpa [resetFirst, resetTable] using (Loop.flow .resetFirst v)

theorem resetSecond_flow (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Flow (resetSecond v).chunk := by
  simpa [resetSecond, resetTable] using (Loop.flow .resetLast v)

theorem resetDiscarded_chunkCodeFacts (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CodeFacts (resetDiscarded v).chunk := by
  simpa [resetDiscarded, resetTable] using (Loop.codeFacts .resetDiscarded v)

theorem resetFirst_chunkCodeFacts (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CodeFacts (resetFirst v).chunk := by
  simpa [resetFirst, resetTable] using (Loop.codeFacts .resetFirst v)

theorem resetSecond_chunkCodeFacts (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CodeFacts (resetSecond v).chunk := by
  simpa [resetSecond, resetTable] using (Loop.codeFacts .resetLast v)

end Sha2.Proofs.Reset

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program Sha2.Proofs.Program X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

private theorem resetDiscarded_tableSites (v : Sha2.Proofs.Wrapper.Variant := .sha256) : ∀ x ∈ (resetDiscarded v).load ++ (resetDiscarded v).cloneIn ++
    (resetDiscarded v).cloneOut ++ (resetDiscarded v).nextSmall ++ (resetDiscarded v).nextLarge,
    x ∈ (Loop.resetDiscarded.sites v) := by
  intro x member
  cases v <;> simp [resetDiscarded, resetTable, site, Loop.sites] at member ⊢
  all_goals grind

private theorem resetFirst_tableSites (v : Sha2.Proofs.Wrapper.Variant := .sha256) : ∀ x ∈ (resetFirst v).load ++ (resetFirst v).cloneIn ++
    (resetFirst v).cloneOut ++ (resetFirst v).nextSmall ++ (resetFirst v).nextLarge,
    x ∈ (Loop.resetFirst.sites v) := by
  intro x member
  cases v <;> simp [resetFirst, resetTable, site, Loop.sites] at member ⊢
  all_goals grind

private theorem resetSecond_tableSites (v : Sha2.Proofs.Wrapper.Variant := .sha256) : ∀ x ∈ (resetSecond v).load ++ (resetSecond v).cloneIn ++
    (resetSecond v).cloneOut ++ (resetSecond v).nextSmall ++ (resetSecond v).nextLarge,
    x ∈ (Loop.resetLast.sites v) := by
  intro x member
  cases v <;> simp [resetSecond, resetTable, site, Loop.sites] at member ⊢
  all_goals grind

theorem resetDiscarded_tableCodeFacts (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.CodeFacts (resetDiscarded v) := by
  apply table_codeFacts (v := v) .resetDiscarded (resetDiscarded v)
  · exact resetDiscarded_tableSites v
  · constructor
    · have h : (resetDiscarded v).head = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100df4 else 0x102a24) - 0x100000) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)
    · have h : (resetDiscarded v).exit = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100ebb else 0x102aeb) - 0x100000) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)

theorem resetFirst_tableCodeFacts (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.CodeFacts (resetFirst v) := by
  apply table_codeFacts (v := v) .resetFirst (resetFirst v)
  · exact resetFirst_tableSites v
  · constructor
    · have h : (resetFirst v).head = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100f31 else 0x102b61) - 0x100000) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)
    · have h : (resetFirst v).exit = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100ff6 else 0x102c26) - 0x100000) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)

theorem resetSecond_tableCodeFacts (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Table.CodeFacts (resetSecond v) := by
  apply table_codeFacts (v := v) .resetLast (resetSecond v)
  · exact resetSecond_tableSites v
  · constructor
    · have h : (resetSecond v).head = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x10123d else 0x102e7d) - 0x100000) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)
    · have h : (resetSecond v).exit = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x1012f6 else 0x102f36) - 0x100000) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)

end Sha2.Proofs.Reset


