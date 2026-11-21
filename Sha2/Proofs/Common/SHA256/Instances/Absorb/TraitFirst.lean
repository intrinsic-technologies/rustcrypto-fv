import Sha2.Proofs.Common.SHA256.Absorb.Table
import Sha2.Proofs.Wrapper.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Absorb

def traitFirst (v : Wrapper.Variant := .sha256) : Table.Layout :=
  { chunk :=
      { initialHash := v.initialHash
        frameBytes := 360
        bufferOffset := 0x0
        registers := ⟨5, 14, 13, 12⟩
        alignedSource := 5
        savedSource := 14
        bulkSave := none
        bufferRestore := (some 13)
        bufferSource := (some 3)
        clobbered := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
        entry := (if v = .sha224 then 0x1015eb else 0x10323b)
        smallExit := (if v = .sha224 then 0x101598 else 0x1031e8)
        largeExit := (if v = .sha224 then 0x101679 else 0x1032c9)
        pc := fun
          | .prepare => (if v = .sha224 then 0x1015eb else 0x10323b)
          | .smallBranch => (if v = .sha224 then 0x1015f9 else 0x103249)
          | .emptyTest => (if v = .sha224 then 0x1015fb else 0x10324b)
          | .emptyBranch => (if v = .sha224 then 0x1015fe else 0x10324e)
          | .smallSetup => (if v = .sha224 then 0x101580 else 0x1031d0)
          | .smallCall => (if v = .sha224 then 0x10158a else 0x1031da)
          | .smallLength => (if v = .sha224 then 0x101590 else 0x1031e0)
          | .smallStore => (if v = .sha224 then 0x101593 else 0x1031e3)
          | .fillSetup => (if v = .sha224 then 0x101600 else 0x103250)
          | .fillCall => (if v = .sha224 then 0x10160b else 0x10325b)
          | .increment => (if v = .sha224 then 0x101611 else 0x103261)
          | .fillCompressSetup => (if v = .sha224 then 0x101616 else 0x103266)
          | .fillCompressCall => (if v = .sha224 then 0x101626 else 0x103276)
          | .clearTail => (if v = .sha224 then 0x10162b else 0x10327b)
          | .restoreSource => (if v = .sha224 then 0x101630 else 0x103280)
          | .count => (if v = .sha224 then 0x101633 else 0x103283)
          | .countBranch => (if v = .sha224 then 0x10163a else 0x10328a)
          | .addBlocks => (if v = .sha224 then 0x10163c else 0x10328c)
          | .bulkSetup => (if v = .sha224 then 0x101641 else 0x103291)
          | .bulkCall => (if v = .sha224 then 0x101649 else 0x103299)
          | .bulkRestore => (if v = .sha224 then 0x10164e else 0x10329e)
          | .splitTail => (if v = .sha224 then 0x10164e else 0x10329e)
          | .tailStore => (if v = .sha224 then 0x101665 else 0x1032b5)
          | .tailSetup => (if v = .sha224 then 0x10166a else 0x1032ba)
          | .tailCall => (if v = .sha224 then 0x101673 else 0x1032c3)
          | .emptySetup => (if v = .sha224 then 0x10167e else 0x1032ce)
        blocks := fun
          | .prepare => [⟨(if v = .sha224 then 0x1015eb else 0x10323b), .prepare ⟨5, 14, 13, 12⟩⟩]
          | .smallBranch => [⟨(if v = .sha224 then 0x1015f9 else 0x103249), .branch 2 (.short 0x85)⟩]
          | .emptyTest => [⟨(if v = .sha224 then 0x1015fb else 0x10324b), .test 13⟩]
          | .emptyBranch => [⟨(if v = .sha224 then 0x1015fe else 0x10324e), .branch 4 (.short 0x7e)⟩]
          | .smallSetup => [⟨(if v = .sha224 then 0x101580 else 0x1031d0), .address 7 (.sib 4 (some 13) 0 .none)⟩, ⟨(if v = .sha224 then 0x101584 else 0x1031d4), .move 6 5⟩, ⟨(if v = .sha224 then 0x101587 else 0x1031d7), .move 2 14⟩]
          | .smallCall => []
          | .smallLength => [⟨(if v = .sha224 then 0x101590 else 0x1031e0), .addTail 14 13⟩]
          | .smallStore => [⟨(if v = .sha224 then 0x101593 else 0x1031e3), .storeTail 14 (.sib 4 none 0 (.d8 0x3f))⟩]
          | .fillSetup => [⟨(if v = .sha224 then 0x101600 else 0x103250), .address 14 (.sib 2 (some 5) 0 .none)⟩, ⟨(if v = .sha224 then 0x101604 else 0x103254), .address 7 (.sib 4 (some 13) 0 .none)⟩, ⟨(if v = .sha224 then 0x101608 else 0x103258), .move 6 5⟩]
          | .fillCall => []
          | .increment => [⟨(if v = .sha224 then 0x101611 else 0x103261), .incrementBlocks (.sib 4 none 0 (.d8 0x60))⟩]
          | .fillCompressSetup => [⟨(if v = .sha224 then 0x101616 else 0x103266), .constant 2 0x1⟩, ⟨(if v = .sha224 then 0x10161b else 0x10326b), .address 7 (.sib 4 none 0 (.d8 0x40))⟩, ⟨(if v = .sha224 then 0x101620 else 0x103270), .move 13 3⟩, ⟨(if v = .sha224 then 0x101623 else 0x103273), .move 6 3⟩]
          | .fillCompressCall => []
          | .clearTail => [⟨(if v = .sha224 then 0x10162b else 0x10327b), .clearTail (.sib 4 none 0 (.d8 0x3f))⟩]
          | .restoreSource => [⟨(if v = .sha224 then 0x101630 else 0x103280), .move 5 14⟩]
          | .count => [⟨(if v = .sha224 then 0x101633 else 0x103283), .count 12⟩]
          | .countBranch => [⟨(if v = .sha224 then 0x10163a else 0x10328a), .branch 4 (.short 0x12)⟩]
          | .addBlocks => [⟨(if v = .sha224 then 0x10163c else 0x10328c), .addBlocks (.sib 4 none 0 (.d8 0x60))⟩]
          | .bulkSetup => [⟨(if v = .sha224 then 0x101641 else 0x103291), .address 7 (.sib 4 none 0 (.d8 0x40))⟩, ⟨(if v = .sha224 then 0x101646 else 0x103296), .move 6 5⟩]
          | .bulkCall => []
          | .bulkRestore => []
          | .splitTail => [⟨(if v = .sha224 then 0x10164e else 0x10329e), .splitTail 5 12⟩]
          | .tailStore => [⟨(if v = .sha224 then 0x101665 else 0x1032b5), .storeTail 12 (.sib 4 none 0 (.d8 0x3f))⟩]
          | .tailSetup => [⟨(if v = .sha224 then 0x10166a else 0x1032ba), .move 7 13⟩, ⟨(if v = .sha224 then 0x10166d else 0x1032bd), .move 6 5⟩, ⟨(if v = .sha224 then 0x101670 else 0x1032c0), .move 2 12⟩]
          | .tailCall => []
          | .emptySetup => [⟨(if v = .sha224 then 0x10167e else 0x1032ce), .move 12 14⟩, ⟨(if v = .sha224 then 0x101681 else 0x1032d1), .move 13 3⟩, ⟨(if v = .sha224 then 0x101684 else 0x1032d4), .count 12⟩, ⟨(if v = .sha224 then 0x10168b else 0x1032db), .branch 5 (.short 0xaf)⟩, ⟨(if v = .sha224 then 0x10168d else 0x1032dd), .jump (.short 0xbf)⟩]
        smallCall := ⟨(if v = .sha224 then 0x10158a else 0x1031da), .memory (.rip (if v = .sha224 then 0xfecf0 else 0xfd0a0))⟩
        fillCall := ⟨(if v = .sha224 then 0x10160b else 0x10325b), .memory (.rip (if v = .sha224 then 0xfec6f else 0xfd01f))⟩
        fillCompressCall := ⟨(if v = .sha224 then 0x101626 else 0x103276), .relative (if v = .sha224 then 0x9eb5 else 0x8265)⟩
        bulkCall := ⟨(if v = .sha224 then 0x101649 else 0x103299), .relative (if v = .sha224 then 0x9e92 else 0x8242)⟩
        tailCall := ⟨(if v = .sha224 then 0x101673 else 0x1032c3), .memory (.rip (if v = .sha224 then 0xfec07 else 0xfcfb7))⟩ }
    clobbered := [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    index := 15
    count := .stack 0x68
    pointerSlot := 0xd8
    lengthSlot := 0xe0
    storedOffset := 0x70
    head := (if v = .sha224 then 0x1015bc else 0x10320c)
    exit := (if v = .sha224 then 0x10168f else 0x1032df)
    load := [⟨(if v = .sha224 then 0x1015bc else 0x10320c), .loadPair 15 5 14 (.d32 0xd8) (.d32 0xe0)⟩, ⟨(if v = .sha224 then 0x1015e5 else 0x103235), .loadTail 13 (.sib 4 none 0 (.d8 0x3f))⟩]
    cloneIn := [⟨(if v = .sha224 then 0x1015d4 else 0x103224), .constant 1 0xd⟩, ⟨(if v = .sha224 then 0x1015d9 else 0x103229), .move 3 13⟩, ⟨(if v = .sha224 then 0x1015dc else 0x10322c), .move 7 13⟩, ⟨(if v = .sha224 then 0x1015df else 0x10322f), .move 6 2⟩, ⟨(if v = .sha224 then 0x1015e2 else 0x103232), .clone⟩]
    cloneOut := [⟨(if v = .sha224 then 0x10159b else 0x1031eb), .incrementIndex 15⟩, ⟨(if v = .sha224 then 0x10159e else 0x1031ee), .constant 1 0xd⟩, ⟨(if v = .sha224 then 0x1015a3 else 0x1031f3), .address 2 (.sib 4 none 0 (.d8 0x70))⟩, ⟨(if v = .sha224 then 0x1015a8 else 0x1031f8), .move 7 2⟩, ⟨(if v = .sha224 then 0x1015ab else 0x1031fb), .move 6 13⟩, ⟨(if v = .sha224 then 0x1015ae else 0x1031fe), .clone⟩, ⟨(if v = .sha224 then 0x1015b1 else 0x103201), .compareIndexStack 15 (.d8 0x68)⟩, ⟨(if v = .sha224 then 0x1015b6 else 0x103206), .branch 4 (.near 0xd3)⟩]
    nextSmall := [⟨(if v = .sha224 then 0x101598 else 0x1031e8), .move 13 3⟩]
    nextLarge := [⟨(if v = .sha224 then 0x101679 else 0x1032c9), .jump (.near 0xffffff1d)⟩] }

theorem traitFirst_wellFormed (v : Wrapper.Variant := .sha256) : Table.WellFormed (traitFirst v) 832 := by
  cases v <;> constructor
  all_goals first
    | (constructor <;> decide +kernel)
    | simp [traitFirst, OffsetsApart]

theorem traitFirst_callTargets (v : Wrapper.Variant := .sha256) : CallTargets (traitFirst v).chunk := by
  cases v <;> constructor <;> intro call member
  all_goals simp [traitFirst] at member
  all_goals first
    | (rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl, by decide +kernel⟩)
    | (rcases member with rfl | rfl <;> exact ⟨_, rfl, by decide +kernel⟩)

end Sha2.Proofs.Common.SHA256.Instances.Absorption
