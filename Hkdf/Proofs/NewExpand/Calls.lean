import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Machine.Interfaces

namespace Hkdf.Proofs.NewExpand

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ExtractPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (salt : Option ByteArray) (ikm : ByteArray) : Prop where
  call : CallPre s boundary 0x10fa80 #v[] #v[registerRegion s .rdi 176] 2264
  saltNull : s.regValue .rsi = 0 ↔ salt = none
  saltLength : ∀ key ∈ salt, (s.regValue .rdx).toNat = key.size
  saltBytes : ∀ key ∈ salt, ValidInput s.external (registerRegion s .rsi key.size) key
  ikmLength : (s.regValue .r8).toNat = ikm.size
  ikmBytes : ValidInput s.external (registerRegion s .rcx ikm.size) ikm
  separation : MemorySeparation #v[registerRegion s .rdi 176, Stack.region s 2264]
    (registerRegion s .rcx ikm.size :: salt.toList.map (fun key => registerRegion s .rsi key.size))

def ExtractContract [Bindings] : Prop :=
  ∀ {s : RamState} {boundary : ReturnBoundary} {salt : Option ByteArray} {ikm : ByteArray},
    ExtractPre s boundary salt ikm → ∃ t : RamState,
      CalleeResult s t boundary 176 2264 ∧
      HmacAt t (s.regValue .rdi + 32) (RFC5869.extract .sha256 salt ikm) ByteArray.empty

def writtenLength (length : Nat) : Nat :=
  if length ≤ 8160 then length else 0

structure ExpandPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (prk info : ByteArray) (infoPtr : BitVec 64) (length : Nat) : Prop where
  call : CallPre s boundary 0x10f250 #v[registerRegion s .rdi 144, registerRegion s .rsi 16]
    #v[] 2264
  keySize : prk.size = 32
  hmac : HmacAt s (s.regValue .rdi) prk ByteArray.empty
  count : s.regValue .rdx = 1
  pointer : (registerRegion s .rsi 8).Word64At s.external infoPtr
  infoLength : (⟨(s.regValue .rsi).toNat + 8, 8⟩ : MemoryRegion).Word64At s.external
    (BitVec.ofNat 64 info.size)
  lengthFits : info.size < 2^64
  lengthArg : (s.regValue .r8).toNat = length
  stackSeparation : MemorySeparation #v[Stack.region s 2264]
    [registerRegion s .rdi 144, registerRegion s .rsi 16]
  infoBytes : 0 < length → length ≤ 8160 →
    ValidInput s.external ⟨infoPtr.toNat, info.size⟩ info
  output : 0 < length → length ≤ 8160 → ValidOutput s.external (registerRegion s .rcx length)
  separation : 0 < length → length ≤ 8160 →
    MemorySeparation #v[registerRegion s .rcx length, Stack.region s 2264]
      [registerRegion s .rdi 144, registerRegion s .rsi 16, ⟨infoPtr.toNat, info.size⟩]

structure ExpandResult [bindings : Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (prk info : ByteArray) (length : Nat) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = (returnBoundary s).rip
  rsp : t.regValue .rsp = (returnBoundary s).rsp
  machine : SupportedMachine bindings t
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t #v[registerRegion s .rcx (writtenLength length), Stack.region s 2264]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  status : (t.regValue .rax).setWidth 8 = (if 8160 < length then 1 else 0)
  output : length ≤ 8160 → ∃ bytes,
    RFC5869.expandFromPrk .sha256 prk info length = .ok bytes ∧
    (registerRegion s .rcx length).HasBytes t.external bytes

def ExpandContract [Bindings] : Prop :=
  ∀ {s : RamState} {boundary : ReturnBoundary} {prk info : ByteArray} {infoPtr : BitVec 64}
    {length : Nat}, ExpandPre s boundary prk info infoPtr length →
    ∃ t : RamState, ExpandResult s t boundary prk info length

end Hkdf.Proofs.NewExpand
