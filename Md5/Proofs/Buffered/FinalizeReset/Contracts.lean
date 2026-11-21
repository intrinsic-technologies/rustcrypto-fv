import Md5.Proofs.Buffered.Invariant
import Md5.Proofs.Block.Frame

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive Variant where
  | saved
  | direct
  deriving DecidableEq

def Variant.stackBytes : Variant → Nat
  | .saved => 384
  | .direct => 368

theorem Variant.stackBytes_bounds (variant : Variant) :
    368 ≤ variant.stackBytes ∧ variant.stackBytes ≤ 384 := by
  cases variant <;> decide

def Variant.address (variant : Variant) (address : BitVec 64) : BitVec 64 :=
  address + match variant with
    | .saved => 0
    | .direct => 0x6b0

def Variant.exit : Variant → BitVec 64
  | .saved => 0x100989
  | .direct => 0x101019

def context (s : RamState) : BitVec 64 := stackPtr s + 8

def stackRegion (s : RamState) (variant : Variant := .saved) : MemoryRegion :=
  ⟨(stackPtr s).toNat - 320, 320 + variant.stackBytes⟩

def outputAddress (s : RamState) : BitVec 64 :=
  (Operand.mem (stackPtr s + 0xb8) : Operand 64).read s

def outputRegion (s : RamState) : MemoryRegion := ⟨(outputAddress s).toNat, 16⟩

def changes (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 15, .flags, .rip,
    .mem (stackPtr s - 320) 320, .mem (stackPtr s + 8) 152,
    .mem (stackPtr s + 0xe8) 16, .mem (stackPtr s + 0x128) 16,
    .mem (outputAddress s) 16]

structure Storage (s : RamState) (variant : Variant := .saved) : Prop where
  stackLow : 320 ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat + variant.stackBytes < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  stackAllocated : (stackRegion s variant).Allocated s.external
  stackAvoids : (stackRegion s variant).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)
  outputBounded : (outputRegion s).Bounded
  outputAllocated : (outputRegion s).Allocated s.external
  outputAvoids : (outputRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)
  outputStack : (outputRegion s).Disjoint (stackRegion s variant)

structure Pre [bindings : Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  stride : UnitStringStride bindings
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  boundaryOutside : ¬ InProgram boundary.rip
  rip : s.RIP = variant.address 0x1007a6
  absorbed : Absorbed (context s) message s
  position : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)
  bitBlocks : (Operand.reg 14 : Operand 64).read s =
    BitVec.ofNat 64 (message.size / 64) <<< 9
  messageBounded : message.size < 2^64

structure Post [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) (variant : Variant := .saved) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = variant.exit
  absorbed : Absorbed (context s) ByteArray.empty t
  digest : (outputRegion s).HasBytes t.external
    ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message)).toArray⟩
  agrees : AgreesExcept (changes s) s t

theorem Post.rsp {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Post boundary message s t variant) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [changes])

theorem Post.rbp {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Post boundary message s t variant) :
    (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s :=
  h.agrees.read (by simp [changes])

theorem Post.r12 {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Post boundary message s t variant) :
    (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
  h.agrees.read (by simp [changes])

end Md5.Proofs.Buffered.FinalizeReset
