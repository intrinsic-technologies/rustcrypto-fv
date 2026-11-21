import P256.Proofs.Sec1.EncodedPoint
import P256.Proofs.Projective.Representation
import P256.Proofs.Program.ScalarFrame.State

set_option autoImplicit false

namespace P256.Proofs.ProjectiveWrapper.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

abbrev entryAddress : BitVec 64 := 0x10ac30

abbrev frameBytes : Nat := 488

abbrev stackBytes : Nat := frameBytes + 8 + 3360

def projective (point : Curve.Point) : Projective :=
  match point with
  | .infinity => ⟨0, 1, 0⟩
  | .affine x y => ⟨x, y, 1⟩

structure InputAt (s : RamState) (address : BitVec 64) (index : Nat)
    (input : Input) : Prop where
  pointerCount : index < (memLoad s.external (address + 8) 64).toNat
  lengthCount : index < (memLoad s.external (address + 24) 64).toNat
  pointersBounded : (⟨(memLoad s.external address 64).toNat, 8 * (index + 1)⟩ : MemoryRegion).Bounded
  lengthsBounded : (⟨(memLoad s.external (address + 16) 64).toNat, 8 * (index + 1)⟩ : MemoryRegion).Bounded
  pointerReadable : MemReadable s (memLoad s.external address 64 + BitVec.ofNat 64 (8 * index)) 8
  lengthReadable : MemReadable s (memLoad s.external (address + 16) 64 + BitVec.ofNat 64 (8 * index)) 8
  pointer : memLoad s.external (memLoad s.external address 64 + BitVec.ofNat 64 (8 * index)) 64 = input.address
  length : memLoad s.external (memLoad s.external (address + 16) 64 + BitVec.ofNat 64 (8 * index)) 64 = BitVec.ofNat 64 input.bytes.size
  nonnull : input.address ≠ 0
  bounded : input.region.Bounded
  bytes : input.region.HasBytes s.external input.bytes

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (index : Nat) (input : Input) (point : Curve.Point) : Prop
    extends CalleePre s boundary entryAddress 32 104 3856 where
  indexArgument : s.regValue .rdx = BitVec.ofNat 64 index
  selected : InputAt s (s.regValue .rsi) index input
  pointerStack : (⟨(memLoad s.external (s.regValue .rsi) 64).toNat,
    8 * (index + 1)⟩ : MemoryRegion).Disjoint (Stack.region s 3856)
  lengthStack : (⟨(memLoad s.external (s.regValue .rsi + 16) 64).toNat,
    8 * (index + 1)⟩ : MemoryRegion).Disjoint (Stack.region s 3856)
  inputStack : input.region.Disjoint (Stack.region s 3856)
  valid : Points.decodePoint input.bytes = some point

structure Result [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Curve.Point) : Prop extends CalleeResult s t boundary 104 3856 where
  tag : memLoad t.external (s.regValue .rdi) 32 = 0
  output : ProjectiveAt t (s.regValue .rdi + 8) (projective point)

structure Filled [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop extends ScalarFrame.FrameState s t 104 3856 488 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10acd9
  output : t.regValue .rbx = s.regValue .rdi
  encoded : Sec1.EncodedPointAt t (stackPtr s - 488) bytes
  zero : t.regValue .r12 = 0

structure Prepared [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop extends ScalarFrame.FrameState s t 104 3856 488 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10ae2a
  output : t.regValue .rbx = s.regValue .rdi
  source : t.regValue .rsi = stackPtr s - 266
  destination : t.regValue .rdi = stackPtr s - 144
  encoded : Sec1.EncodedPointAt t (stackPtr s - 266) bytes
  zero : t.regValue .r12 = 0

structure Decoded [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Curve.Point) : Prop extends ScalarFrame.FrameState s t 104 3856 488 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10ae2f
  output : t.regValue .rbx = s.regValue .rdi
  affine : Sec1.AffineResultAt t (stackPtr s - 144) (some point)
  zero : t.regValue .r12 = 0

end P256.Proofs.ProjectiveWrapper.Decode
