import Hkdf.Proofs.NewExpand.Calls
import Hkdf.Proofs.Common.CallFrame

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SavedFrame (initial s : RamState) : Prop where
  rbp : s.regValue .rbp = initial.regValue .rbp
  rbx : memLoad s.external (stackPtr initial - 40) 64 = initial.regValue .rbx
  r12 : memLoad s.external (stackPtr initial - 32) 64 = initial.regValue .r12
  r13 : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .r13
  r14 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r14
  r15 : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .r15
  ret : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip

structure Arguments (initial s : RamState) : Prop where
  info : s.regValue .r14 = initial.regValue .r8
  infoLength : s.regValue .rbx = initial.regValue .r9
  output : s.regValue .r15 = stackArgument initial 1
  length : s.regValue .r12 = stackArgument initial 2

abbrev Running [Bindings] (initial s : RamState) :=
  CallFrame.Running initial (returnBoundary initial)
    #v[Stack.region initial hkdfSha256NewExpandMinStackBytes] s

structure ExtractEntry [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (ikm : ByteArray) : Prop where
  run : Running initial s
  pre : ExtractPre s (returnBoundary initial) salt ikm
  saved : SavedFrame initial s
  args : Arguments initial s
  rsp : stackPtr s = stackPtr initial - 368
  dest : s.regValue .rdi = stackPtr initial - 360
  boundary : returnBoundary s = ⟨0x10200a, stackPtr initial - 360⟩

structure ExtractReturn [Bindings] (initial s : RamState) (prk : ByteArray) : Prop where
  run : Running initial s
  saved : SavedFrame initial s
  args : Arguments initial s
  rsp : stackPtr s = stackPtr initial - 360
  rip : s.RIP = 0x10200a
  hmac : HmacAt s (stackPtr initial - 328) prk ByteArray.empty

structure ExpandEntry [Bindings] (initial s : RamState) (prk info : ByteArray) (length : Nat) :
    Prop where
  run : Running initial s
  pre : ExpandPre s (returnBoundary initial) prk info (initial.regValue .r8) length
  saved : SavedFrame initial s
  rsp : stackPtr s = stackPtr initial - 368
  output : s.regValue .rcx = stackArgument initial 1
  boundary : returnBoundary s = ⟨0x102044, stackPtr initial - 360⟩

end Hkdf.Proofs.NewExpand.Wrapper
