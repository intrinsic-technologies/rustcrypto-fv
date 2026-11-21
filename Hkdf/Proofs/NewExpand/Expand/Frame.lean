import Hkdf.Proofs.NewExpand.Calls
import Hkdf.Proofs.Common.CallFrame

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def slot (s : RamState) (offset : BitVec 64) : BitVec 64 :=
  (Operand.mem (s.regValue .rsp + offset) : Operand 64).read s

structure SavedFrame [Bindings] (entry s : RamState) (boundary : ReturnBoundary) (length : Nat) : Prop
    extends Common.CallFrame.Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] s where
  sp : s.regValue .rsp = entry.regValue .rsp - 536
  rbx : slot s 488 = entry.regValue .rbx
  r12 : slot s 496 = entry.regValue .r12
  r13 : slot s 504 = entry.regValue .r13
  r14 : slot s 512 = entry.regValue .r14
  r15 : slot s 520 = entry.regValue .r15
  rbp : slot s 528 = entry.regValue .rbp
  ret : slot s 536 = (returnBoundary entry).rip
  size : slot s 224 = BitVec.ofNat 64 length
  mxcsr : s.MXCSR = entry.MXCSR
  fcw : s.FP87_Control = entry.FP87_Control

theorem SavedFrame.of_agreement [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {length : Nat} (saved : SavedFrame entry s boundary length)
    (running : Common.CallFrame.Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] t)
    (sp : t.regValue .rsp = s.regValue .rsp)
    (same : (Component.mem (s.regValue .rsp + 488) 56).Agrees s t)
    (sameLength : slot t 224 = slot s 224)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    SavedFrame entry t boundary length := by
  have words := Common.CallFrame.agrees_memLoad_slots same
    [0, 8, 16, 24, 32, 40, 48] id (by decide)
  have keep (offset : Nat) (member : offset ∈ [0, 8, 16, 24, 32, 40, 48]) :
      slot t (488 + BitVec.ofNat 64 offset) = slot s (488 + BitVec.ofNat 64 offset) := by
    change memLoad t.external (t.regValue .rsp + _) 64 = memLoad s.external (s.regValue .rsp + _) 64
    rw [sp]
    simpa only [id_eq, BitVec.add_assoc] using words offset member
  exact {
    toRunning := running
    sp := sp.trans saved.sp
    rbx := (keep 0 (by decide)).trans saved.rbx
    r12 := (keep 8 (by decide)).trans saved.r12
    r13 := (keep 16 (by decide)).trans saved.r13
    r14 := (keep 24 (by decide)).trans saved.r14
    r15 := (keep 32 (by decide)).trans saved.r15
    rbp := (keep 40 (by decide)).trans saved.rbp
    ret := (keep 48 (by decide)).trans saved.ret
    size := sameLength.trans saved.size
    mxcsr := mxcsr.trans saved.mxcsr
    fcw := fcw.trans saved.fcw }

structure DispatchState [Bindings] (entry s : RamState) (boundary : ReturnBoundary) (length : Nat) : Prop
    extends SavedFrame entry s boundary length where
  pc : s.RIP = (if length = 0 ∨ 8160 < length then 0x10f290 else 0x10f2b1)
  outputPtr : s.regValue .rcx = entry.regValue .rcx
  descriptors : slot s 232 = entry.regValue .rsi
  contextPtr : slot s 240 = entry.regValue .rdi
  count : slot s 248 = entry.regValue .rdx
  stackFrame : MemoryWriteFrame entry s #v[Stack.region entry 2264]

end Hkdf.Proofs.NewExpand.Expand
