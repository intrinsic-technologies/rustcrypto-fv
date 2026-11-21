import Sha2.Proofs.Common.SHA256.Instances.Absorb.Code
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Headers
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitFirst

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Sha2.Proofs.Program X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

private def site (pc : Nat) (block : Blocks.Block) : Blocks.Site :=
  ⟨BitVec.ofNat 64 pc, block⟩

private def table (loop : Loop) (clobbered : List (BitVec 5)) (index : BitVec 4)
    (count : Table.Count) (pointerSlot lengthSlot storedOffset head exit : Nat)
    (load cloneIn cloneOut nextSmall nextLarge : List Blocks.Site) (v : Wrapper.Variant) : Table.Layout :=
  { chunk := loop.chunk v
    clobbered := clobbered
    index := index
    count := count
    pointerSlot := pointerSlot
    lengthSlot := lengthSlot
    storedOffset := storedOffset
    head := BitVec.ofNat 64 head
    exit := BitVec.ofNat 64 exit
    load := load
    cloneIn := cloneIn
    cloneOut := cloneOut
    nextSmall := nextSmall
    nextLarge := nextLarge }

def finalizeFirstTable (v : Wrapper.Variant := .sha256) : Table.Layout :=
  table .finalizeFirst
    [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
    14 (.reg 15) 0xd8 0xe0 8 (if v = .sha224 then 0x100708 else 0x102318) (if v = .sha224 then 0x1007d7 else 0x1023e7)
    [site (if v = .sha224 then 0x100708 else 0x102318) (.loadPair 14 13 5 (.d32 0xd8) (.d32 0xe0)),
      site (if v = .sha224 then 0x100720 else 0x102330) (.loadTail 12 (.sib 4 none 0 (.d8 0x47)))] [] []
    [site (if v = .sha224 then 0x1006fc else 0x10230c) (.incrementIndex 14), site (if v = .sha224 then 0x1006ff else 0x10230f) (.compareIndex 14 15),
      site (if v = .sha224 then 0x100702 else 0x102312) (.branch 4 (.near 0xcf))]
    [site (if v = .sha224 then 0x1007bb else 0x1023cb) (.incrementIndex 14), site (if v = .sha224 then 0x1007be else 0x1023ce) (.compareIndex 14 15),
      site (if v = .sha224 then 0x1007c1 else 0x1023d1) (.branch 5 (.near 0xffffff41)), site (if v = .sha224 then 0x1007c7 else 0x1023d7) (.jump (.short 0xe))] v

def finalizeLastTable (v : Wrapper.Variant := .sha256) : Table.Layout :=
  table .finalizeLast
    [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
    14 (.reg 15) 0xd8 0xe0 8 (if v = .sha224 then 0x100a22 else 0x102642) (if v = .sha224 then 0x100ae8 else 0x102708)
    [site (if v = .sha224 then 0x100a22 else 0x102642) (.loadPair 14 6 13 (.d32 0xd8) (.d32 0xe0)),
      site (if v = .sha224 then 0x100a3a else 0x10265a) (.loadTail 3 (.sib 4 none 0 (.d8 0x47)))] [] []
    [site (if v = .sha224 then 0x100a16 else 0x102636) (.incrementIndex 14), site (if v = .sha224 then 0x100a19 else 0x102639) (.compareIndex 14 15),
      site (if v = .sha224 then 0x100a1c else 0x10263c) (.branch 4 (.near 0xc6))]
    [site (if v = .sha224 then 0x100acc else 0x1026ec) (.incrementIndex 14), site (if v = .sha224 then 0x100acf else 0x1026ef) (.compareIndex 14 15),
      site (if v = .sha224 then 0x100ad2 else 0x1026f2) (.branch 5 (.near 0xffffff4a)), site (if v = .sha224 then 0x100ad8 else 0x1026f8) (.jump (.short 0xe))] v

def traitLastTable (v : Wrapper.Variant := .sha256) : Table.Layout :=
  table .traitLast
    [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    15 (.stack 0x68) 0xd8 0xe0 0x70 (if v = .sha224 then 0x10192c else 0x10358c) (if v = .sha224 then 0x1019fe else 0x10365e)
    [site (if v = .sha224 then 0x10192c else 0x10358c) (.loadPair 15 13 12 (.d32 0xd8) (.d32 0xe0)),
      site (if v = .sha224 then 0x101955 else 0x1035b5) (.loadTail 5 (.sib 4 none 0 (.d8 0x3f)))]
    [site (if v = .sha224 then 0x101944 else 0x1035a4) (.constant 1 0xd), site (if v = .sha224 then 0x101949 else 0x1035a9) (.move 3 5),
      site (if v = .sha224 then 0x10194c else 0x1035ac) (.move 7 5), site (if v = .sha224 then 0x10194f else 0x1035af) (.move 6 2), site (if v = .sha224 then 0x101952 else 0x1035b2) .clone]
    [site (if v = .sha224 then 0x10190b else 0x10356b) (.incrementIndex 15), site (if v = .sha224 then 0x10190e else 0x10356e) (.constant 1 0xd),
      site (if v = .sha224 then 0x101913 else 0x103573) (.address 2 (.sib 4 none 0 (.d8 0x70))), site (if v = .sha224 then 0x101918 else 0x103578) (.move 7 2),
      site (if v = .sha224 then 0x10191b else 0x10357b) (.move 6 5), site (if v = .sha224 then 0x10191e else 0x10357e) .clone,
      site (if v = .sha224 then 0x101921 else 0x103581) (.compareIndexStack 15 (.d8 0x68)),
      site (if v = .sha224 then 0x101926 else 0x103586) (.branch 4 (.near 0xd2))]
    [site (if v = .sha224 then 0x101908 else 0x103568) (.move 5 3)]
    [site (if v = .sha224 then 0x1019e8 else 0x103648) (.jump (.near 0xffffff1e))] v

theorem finalizeFirstTable_wellFormed (v : Wrapper.Variant := .sha256) : Table.WellFormed (finalizeFirstTable v) 832 := by
  constructor
  · exact Loop.wellFormed .finalizeFirst v
  all_goals simp [finalizeFirstTable, table, Loop.chunk, X86Proofs.OffsetsApart]

theorem finalizeLastTable_wellFormed (v : Wrapper.Variant := .sha256) : Table.WellFormed (finalizeLastTable v) 832 := by
  constructor
  · exact Loop.wellFormed .finalizeLast v
  all_goals simp [finalizeLastTable, table, Loop.chunk, X86Proofs.OffsetsApart]

theorem traitLastTable_wellFormed (v : Wrapper.Variant := .sha256) : Table.WellFormed (traitLastTable v) 832 := by
  constructor
  · exact Loop.wellFormed .traitLast v
  all_goals simp [traitLastTable, table, Loop.chunk, X86Proofs.OffsetsApart]

theorem finalizeFirstTable_callTargets (v : Wrapper.Variant := .sha256) : CallTargets (finalizeFirstTable v).chunk := by
  simpa [finalizeFirstTable, table] using (Loop.callTargets .finalizeFirst v)

theorem finalizeLastTable_callTargets (v : Wrapper.Variant := .sha256) : CallTargets (finalizeLastTable v).chunk := by
  simpa [finalizeLastTable, table] using (Loop.callTargets .finalizeLast v)

theorem traitLastTable_callTargets (v : Wrapper.Variant := .sha256) : CallTargets (traitLastTable v).chunk := by
  simpa [traitLastTable, table] using (Loop.callTargets .traitLast v)

theorem finalizeFirstTable_flow (v : Wrapper.Variant := .sha256) : Flow (finalizeFirstTable v).chunk := by
  simpa [finalizeFirstTable, table] using (Loop.flow .finalizeFirst v)

theorem finalizeLastTable_flow (v : Wrapper.Variant := .sha256) : Flow (finalizeLastTable v).chunk := by
  simpa [finalizeLastTable, table] using (Loop.flow .finalizeLast v)

theorem traitLastTable_flow (v : Wrapper.Variant := .sha256) : Flow (traitLastTable v).chunk := by
  simpa [traitLastTable, table] using (Loop.flow .traitLast v)

theorem finalizeFirstTable_chunkCodeFacts (v : Wrapper.Variant := .sha256) : CodeFacts (finalizeFirstTable v).chunk := by
  simpa [finalizeFirstTable, table] using (Loop.codeFacts .finalizeFirst v)

theorem finalizeLastTable_chunkCodeFacts (v : Wrapper.Variant := .sha256) : CodeFacts (finalizeLastTable v).chunk := by
  simpa [finalizeLastTable, table] using (Loop.codeFacts .finalizeLast v)

theorem traitLastTable_chunkCodeFacts (v : Wrapper.Variant := .sha256) : CodeFacts (traitLastTable v).chunk := by
  simpa [traitLastTable, table] using (Loop.codeFacts .traitLast v)

private theorem finalizeFirstTable_sites (v : Wrapper.Variant := .sha256) : ∀ x ∈ (finalizeFirstTable v).load ++ (finalizeFirstTable v).cloneIn ++
    (finalizeFirstTable v).cloneOut ++ (finalizeFirstTable v).nextSmall ++ (finalizeFirstTable v).nextLarge,
    x ∈ (Loop.finalizeFirst.sites v) := by
  cases v
  all_goals
    intro x member
    simp [finalizeFirstTable, table, site, Loop.sites] at member ⊢
    rcases member with h | h | h | h | h | h | h | h | h
    all_goals rw [h] <;> simp

theorem table_codeFacts (loop : Loop) (l : Table.Layout) (v : Wrapper.Variant := .sha256)
    (sites : ∀ x ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge,
      x ∈ (loop.sites v)) (inside : InProgram l.head ∧ InProgram l.exit) : Table.CodeFacts l := by
  constructor
  · intro x member s loaded
    exact loop.sites_loaded s loaded v x (sites x member)
  · exact inside

theorem finalizeFirstTable_codeFacts (v : Wrapper.Variant := .sha256) : Table.CodeFacts (finalizeFirstTable v) := by
  apply table_codeFacts (v := v) .finalizeFirst (finalizeFirstTable v)
  · exact finalizeFirstTable_sites v
  · constructor
    · have h : (finalizeFirstTable v).head = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100708 else 0x102318) - (if v = .sha224 then 0x100000 else 0x100000)) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)
    · have h : (finalizeFirstTable v).exit = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x1007d7 else 0x1023e7) - (if v = .sha224 then 0x100000 else 0x100000)) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)

private theorem finalizeLastTable_sites (v : Wrapper.Variant := .sha256) : ∀ x ∈ (finalizeLastTable v).load ++ (finalizeLastTable v).cloneIn ++
    (finalizeLastTable v).cloneOut ++ (finalizeLastTable v).nextSmall ++ (finalizeLastTable v).nextLarge,
    x ∈ (Loop.finalizeLast.sites v) := by
  cases v
  all_goals
    intro x member
    simp [finalizeLastTable, table, site, Loop.sites] at member ⊢
    grind

private theorem traitLastTable_sites (v : Wrapper.Variant := .sha256) : ∀ x ∈ (traitLastTable v).load ++ (traitLastTable v).cloneIn ++
    (traitLastTable v).cloneOut ++ (traitLastTable v).nextSmall ++ (traitLastTable v).nextLarge,
    x ∈ (Loop.traitLast.sites v) := by
  cases v
  all_goals
    intro x member
    simp [traitLastTable, table, site, Loop.sites] at member ⊢
    grind

theorem finalizeLastTable_codeFacts (v : Wrapper.Variant := .sha256) : Table.CodeFacts (finalizeLastTable v) := by
  apply table_codeFacts (v := v) .finalizeLast (finalizeLastTable v)
  · exact finalizeLastTable_sites v
  · constructor
    · have h : (finalizeLastTable v).head = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100a22 else 0x102642) - (if v = .sha224 then 0x100000 else 0x100000)) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)
    · have h : (finalizeLastTable v).exit = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x100ae8 else 0x102708) - (if v = .sha224 then 0x100000 else 0x100000)) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)

theorem traitLastTable_codeFacts (v : Wrapper.Variant := .sha256) : Table.CodeFacts (traitLastTable v) := by
  apply table_codeFacts (v := v) .traitLast (traitLastTable v)
  · exact traitLastTable_sites v
  · constructor
    · have h : (traitLastTable v).head = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x10192c else 0x10358c) - (if v = .sha224 then 0x100000 else 0x100000)) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)
    · have h : (traitLastTable v).exit = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x1019fe else 0x10365e) - (if v = .sha224 then 0x100000 else 0x100000)) := by
        cases v <;> decide +kernel
      rw [h]
      exact inProgram_of_textOffset _ (by cases v <;> decide)

end Sha2.Proofs.Common.SHA256.Instances.Absorption
