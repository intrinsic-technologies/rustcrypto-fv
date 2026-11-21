import Sha2.Proofs.Common.SHA256.Finalize.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Finalize

inductive Finalization where
  | digest
  | resetFirst
  | resetLast
  | finalizeFirst
  | finalizeLast
  | traitFirst
  | traitLast

def Finalization.variant : Finalization → Variant
  | .digest => .digest
  | .resetFirst | .resetLast => .reset
  | .finalizeFirst => .finalizeFirst
  | .finalizeLast => .finalizeLast
  | .traitFirst => .traitFirst
  | .traitLast => .traitLast

def Finalization.entry (occ : Finalization)
    (hashVariant : Sha2.Proofs.Wrapper.Variant := .sha256) : Nat :=
  match hashVariant, occ with
  | .sha224, .digest => 0x100105
  | .sha224, .resetFirst => 0x101026
  | .sha224, .resetLast => 0x10130f
  | .sha224, .finalizeFirst => 0x1007f8
  | .sha224, .finalizeLast => 0x100b13
  | .sha224, .traitFirst => 0x1016be
  | .sha224, .traitLast => 0x101a1e
  | .sha256, .digest => 0x101cf5
  | .sha256, .resetFirst => 0x102c56
  | .sha256, .resetLast => 0x102f4f
  | .sha256, .finalizeFirst => 0x102408
  | .sha256, .finalizeLast => 0x102733
  | .sha256, .traitFirst => 0x10330e
  | .sha256, .traitLast => 0x10367e

def Finalization.frameBytes : Finalization → Nat
  | .digest => 312
  | .resetFirst | .resetLast => 248
  | _ => 360

def Finalization.reserve : Finalization → Nat
  | .digest => 784
  | .resetFirst | .resetLast => 720
  | _ => 832

def Finalization.layout (occ : Finalization)
    (hashVariant : Sha2.Proofs.Wrapper.Variant := .sha256) : Layout :=
  let v := occ.variant
  let entry := occ.entry hashVariant
  let fill := entry + (Mark.bytes v).length
  let branch := fill + 6
  let firstHead := branch + (Branch.bytes v 0).length
  let firstLower := firstHead + (FirstHead.bytes v).length
  let firstSetup := firstLower + (Lower.bytes v).length
  let firstCall := firstSetup + (Setup.bytes v false).length
  let zeroPC := firstCall + 5
  let length := zeroPC + v.buffer.length
  let lastHead := length + v.registers.length
  let lastLower := lastHead + (LastHead.bytes v).length
  let lastSetup := lastLower + (Lower.bytes v).length
  let lastCall := lastSetup + (Setup.bytes v true).length
  { variant := v
    hashVariant := hashVariant
    frameBytes := occ.frameBytes
    entry := BitVec.ofNat 64 entry
    fillCall := BitVec.ofNat 64 fill
    branch := BitVec.ofNat 64 branch
    firstHead := BitVec.ofNat 64 firstHead
    firstLower := BitVec.ofNat 64 firstLower
    firstSetup := BitVec.ofNat 64 firstSetup
    firstCall := BitVec.ofNat 64 firstCall
    zero := BitVec.ofNat 64 zeroPC
    length := BitVec.ofNat 64 length
    lastHead := BitVec.ofNat 64 lastHead
    lastLower := BitVec.ofNat 64 lastLower
    lastSetup := BitVec.ofNat 64 lastSetup
    lastCall := BitVec.ofNat 64 lastCall
    exit := BitVec.ofNat 64 (lastCall + 5)
    fillDisp := BitVec.ofNat 32 (0x200288 - (fill + 6))
    branchDisp := BitVec.ofNat 32 (length - (branch + (Branch.bytes v 0).length))
    firstDisp := BitVec.ofNat 32 (0x10b4e0 - (firstCall + 5))
    lastDisp := BitVec.ofNat 32 (0x10b4e0 - (lastCall + 5)) }

theorem Finalization.wellFormed (occ : Finalization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) :
    WellFormed (occ.layout v) occ.reserve := by
  cases v <;> cases occ <;> constructor <;> decide +kernel

theorem Finalization.flow (occ : Finalization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Flow (occ.layout v) := by
  cases v <;> cases occ <;> constructor <;> decide +kernel

theorem Finalization.codeFacts (occ : Finalization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : CodeFacts (occ.layout v) := by
  constructor
  · intro stage s loaded
    let offset := (Stage.pc stage (occ.layout v)).toNat - 0x100000
    have pc : Stage.pc stage (occ.layout v) = Extracted.textAddress + BitVec.ofNat 64 offset := by
      cases v <;> cases occ <;> cases stage <;> decide +kernel
    rw [pc]
    apply programText_slice (programLoaded_codeIn loaded) offset (Stage.bytes stage (occ.layout v))
    · cases v <;> cases occ <;> cases stage <;> decide +kernel
    · cases v <;> cases occ <;> cases stage <;> decide +kernel
  · intro stage
    let offset := (Stage.pc stage (occ.layout v)).toNat - 0x100000
    have pc : Stage.pc stage (occ.layout v) = Extracted.textAddress + BitVec.ofNat 64 offset := by
      cases v <;> cases occ <;> cases stage <;> decide +kernel
    rw [pc]
    apply blockInProgram_of_textOffset
    cases v <;> cases occ <;> cases stage <;> decide +kernel

end Sha2.Proofs.Common.SHA256.Instances
