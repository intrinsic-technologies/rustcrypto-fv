import P256.Proofs.Sec1Serialize.Tail.State
import P256.Proofs.Sec1Serialize.Conversion.Stage
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Selection

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open Conversion (Stage)

structure LoopState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : Nat → UInt8) (infinity : Bool) (index : Nat) : Prop where
  stage : Stage s s t boundary
  rip : t.RIP = if index < 65 then 0x1111a0 else 0x1111ce
  choice : (t.regValue .rax).setWidth 8 = if infinity then 1 else 0
  counter : t.regValue .rdx = BitVec.ofNat 64 index
  destination : t.regValue .rbp = s.regValue .rdi
  source : Bytes t.external (stackPtr s - 113) 65 bytes
  zeroSource : Bytes t.external (stackPtr s - 184) 65 (fun _ => 0)
  selected : Bytes t.external (stackPtr s - 296) index (fun i => if infinity then 0 else bytes i)

structure Loaded [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : Nat → UInt8) (infinity : Bool) (index : Nat) : Prop where
  stage : Stage s s t boundary
  rip : t.RIP = 0x1111ba
  choice : (t.regValue .rax).setWidth 8 = if infinity then 1 else 0
  counter : t.regValue .rdx = BitVec.ofNat 64 index
  destination : t.regValue .rbp = s.regValue .rdi
  source : Bytes t.external (stackPtr s - 113) 65 bytes
  zeroSource : Bytes t.external (stackPtr s - 184) 65 (fun _ => 0)
  selected : Bytes t.external (stackPtr s - 296) index (fun i => if infinity then 0 else bytes i)
  byte : t.regValue .rsi = (bytes index).toBitVec.setWidth 64
  zeroByte : t.regValue .rdi = 0
  flag : t.regValue .r8 = if infinity then 1 else 0

structure Stored [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : Nat → UInt8) (infinity : Bool) (index : Nat) : Prop where
  stage : Stage s s t boundary
  rip : t.RIP = 0x1111c5
  choice : (t.regValue .rax).setWidth 8 = if infinity then 1 else 0
  counter : t.regValue .rdx = BitVec.ofNat 64 index
  destination : t.regValue .rbp = s.regValue .rdi
  source : Bytes t.external (stackPtr s - 113) 65 bytes
  zeroSource : Bytes t.external (stackPtr s - 184) 65 (fun _ => 0)
  selected : Bytes t.external (stackPtr s - 296) (index+1) (fun i => if infinity then 0 else bytes i)

end P256.Proofs.Sec1Serialize.Selection
