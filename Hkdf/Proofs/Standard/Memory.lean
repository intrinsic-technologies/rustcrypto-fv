import Hkdf.Proofs.Standard.State
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Machine
import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.Machine.Entry
import Hkdf.Proofs.Common.Encoding.Serialize.Stack
import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Machine.StackRegion

set_option autoImplicit false

namespace Hkdf.Proofs.Standard

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_bounds [Bindings] {initial : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) :
    1792 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 :=
  Hkdf.Proofs.Common.CallFrame.stack_bounds ctx.call.stack

theorem initial_stack_readable [Bindings] {initial : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) {offset len : Nat}
    (low : offset ≤ 1792) (high : len ≤ offset + 8) :
    MemReadable initial (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_readable ctx.call.stack (fun _ h ↦ h) low high

theorem initial_stack_writable [Bindings] {initial : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) {offset len : Nat}
    (low : offset ≤ 1792) (high : len ≤ offset + 8) (positive : 0 < len)
    (page : (stackPtr initial - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_writable ctx.call.stack
    ((ctx.call.stackSeparation.2 _ (by simp)).2) (fun _ h ↦ h) low high positive page

theorem initial_stack_writable8 [Bindings] {initial : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) {offset : Nat}
    (low : offset ≤ 1792) (align : offset % 8 = 0) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
  Hkdf.Proofs.Common.CallFrame.stack_writable8 ctx.call.stack
    ((ctx.call.stackSeparation.2 _ (by simp)).2) (fun _ h ↦ h) low align

theorem stack_codeApart [Bindings] {initial : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    {offset len codeOffset codeLen : Nat} (low : offset ≤ 1792) (high : len ≤ offset)
    (bound : codeOffset + codeLen ≤ 115149) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen :=
  Hkdf.Proofs.Common.CallFrame.stack_codeApart ctx.call.stack
    (fun a ha hp ↦ (ctx.call.stackSeparation.2 _ (by simp)).2 a ha (.inl hp))
    low (by omega) bound

theorem stack_readable [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) (state : State initial s)
    {offset len : Nat} (low : offset ≤ 1792) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Hkdf.Proofs.Common.CallFrame.stack_readable ctx.call.stack state.allocated low high

theorem stack_address {initial s : RamState} (rsp : s.regValue .rsp = frameBase initial)
    {offset : Nat} (bound : offset ≤ 520) :
    rspOf s + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
  change s.regValue .rsp + _ = _
  rw [rsp, frameBase]
  change initial.regValue .rsp - 520 + BitVec.ofNat 64 offset =
    initial.regValue .rsp - BitVec.ofNat 64 (520 - offset)
  rw [← BitVec.ofNat_sub_ofNat_of_le 520 offset (by omega) bound]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc,
    BitVec.ofNat_eq_ofNat]

theorem returnBoundary_valid [bindings : Bindings] {initial : RamState}
    {salt : Option ByteArray} {inputs : Array Input} (ctx : Context initial salt inputs) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      (returnBoundary initial).rip.toNat < userAddressLimit ∧
      ¬ InProgram (returnBoundary initial).rip :=
  Hkdf.Proofs.Common.Machine.returnBoundary_valid
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep
      (Hkdf.Proofs.Program.SupportedMachine.of_root bindings initial ctx.machine ctx.environment))
    ctx.call.stack ctx.call.returnAddress

end Hkdf.Proofs.Standard
