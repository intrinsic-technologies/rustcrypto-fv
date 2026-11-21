import Sha2.Proofs.Common.SHA256.Blocks.Zero
import Sha2.Proofs.Common.SHA256.Blocks.Length
import Sha2.Proofs.Wrapper.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive Variant where
  | digest
  | reset
  | finalizeFirst
  | finalizeLast
  | traitFirst
  | traitLast
  deriving DecidableEq

def Variant.buffer : Variant → Blocks.Zero.Offset
  | .digest | .reset | .traitLast => .zero
  | .finalizeFirst => .eight
  | .finalizeLast | .traitFirst => .oneTwelve

def Variant.scratch : Variant → Nat
  | .digest | .reset => 104
  | .finalizeFirst => 112
  | .finalizeLast | .traitLast => 232
  | .traitFirst => 0

def Variant.registers : Variant → Blocks.Length.Registers
  | .digest => .r13_r12
  | .reset | .traitFirst => .r14_r15
  | .finalizeFirst => .r14_r12
  | .finalizeLast | .traitLast => .r12_r15

def Variant.padReg : Variant → BitVec 5
  | .digest => 15
  | .reset | .finalizeFirst | .traitFirst => 3
  | .finalizeLast | .traitLast => 14

def Variant.hashReg : Variant → BitVec 5
  | .digest => 14
  | .traitFirst => 5
  | .reset | .finalizeFirst | .finalizeLast | .traitLast => 3

def Variant.needsHashPointer : Variant → Bool
  | .reset | .finalizeFirst => false
  | _ => true

def Variant.clobbered (v : Variant) : List (BitVec 5) :=
  [0, 1, 2, 6, 7, 8, 9, 10, 11, v.registers.tail, v.padReg] ++
    (if v.registers.preShifted then [] else [v.registers.blocks]) ++
    (if v = .reset ∨ v = .finalizeFirst then [v.hashReg] else [])

structure Layout where
  variant : Variant
  frameBytes : Nat
  entry : BitVec 64
  fillCall : BitVec 64
  branch : BitVec 64
  firstHead : BitVec 64
  firstLower : BitVec 64
  firstSetup : BitVec 64
  firstCall : BitVec 64
  zero : BitVec 64
  length : BitVec 64
  lastHead : BitVec 64
  lastLower : BitVec 64
  lastSetup : BitVec 64
  lastCall : BitVec 64
  exit : BitVec 64
  fillDisp : BitVec 32
  branchDisp : BitVec 32
  firstDisp : BitVec 32
  lastDisp : BitVec 32
  hashVariant : Sha2.Proofs.Wrapper.Variant := .sha256

def Layout.sp (L : Layout) (initial : RamState) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 L.frameBytes

def Layout.buffer (L : Layout) (sp : BitVec 64) : BitVec 64 :=
  sp + BitVec.ofNat 64 L.variant.buffer.value

def Layout.hash (L : Layout) (sp : BitVec 64) : BitVec 64 :=
  L.buffer sp + 64

def Layout.scratch (L : Layout) (sp : BitVec 64) : BitVec 64 :=
  sp + BitVec.ofNat 64 L.variant.scratch

def footprint (L : Layout) (sp : BitVec 64) : Vector MemoryRegion 4 :=
  #v[⟨(L.buffer sp).toNat, 64⟩, ⟨(L.hash sp).toNat, 32⟩,
    ⟨(L.scratch sp).toNat, 64⟩, ⟨(sp - 344).toNat, 344⟩]

structure WellFormed (L : Layout) (reserve : Nat) : Prop where
  capacity : L.frameBytes + 344 ≤ reserve
  aligned : (L.frameBytes + 8) % 16 = 0
  bufferFits : L.variant.buffer.value + 104 ≤ L.frameBytes
  scratchFits : L.variant.scratch + 64 ≤ L.frameBytes
  hashAligned : (L.variant.buffer.value + 64) % 4 = 0
  disjoint : L.variant.buffer.value + 96 ≤ L.variant.scratch ∨
    L.variant.scratch + 64 ≤ L.variant.buffer.value

end Sha2.Proofs.Common.SHA256.Finalize
