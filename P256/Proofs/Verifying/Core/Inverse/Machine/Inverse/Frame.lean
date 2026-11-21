import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.Machine.Program
import P256.Proofs.Field.Inverse.SafeGcd.Frame

namespace P256.Proofs.Verifying.Core.Inverse.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

namespace Inverse

def frameInfo : Refine.FrameInfo where
  entry := 0x112fd0
  frameBytes := 0x38
  stackBytes := some 0x300
  slots := [(3, 0x8)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 51]
  clobbers := []
  callSlots := []

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l115020 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15)], [], []⟩
  | _ => none

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l115020 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x300) 0x300,
       .fact (fr.low.toNat + 0x300 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g0 l => labelFrameG0 l

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15]

theorem frameAt_canonical (l : Label) (fr : Refine.Activation) :
    frameAt l fr = frameInfo.atomsAt (labelFrame l) fr := by
  cases l <;> rename_i l <;> first | rfl | (cases l <;> rfl)

theorem doneAt_canonical (fr : Refine.Activation) : doneAt fr = P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.doneAtoms frameInfo fr := rfl

abbrev Pre (code : CodeMap) (fr : Refine.Activation) (s : RamState) : Prop :=
  P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.Pre frameInfo code fr s

abbrev Post (fr : Refine.Activation) (footprint : List Prelude.MemoryRegion)
    (t : RamState) : Prop :=
  P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.Post frameInfo fr footprint t

end Inverse

end P256.Proofs.Verifying.Core.Inverse.Machine
