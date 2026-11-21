import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.CallFrame.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {salt : Option ByteArray} {ikm : ByteArray}

theorem stackAvoid (pre : ExtractPre initial boundary salt ikm) :
    ∀ region ∈ #v[Stack.region initial 2264], region.Avoids InProgram := by
  intro region member a inside program
  rcases Vector.mem_singleton.mp member with rfl
  exact pre.call.stackAvoid a inside (.inl program)

theorem registerFrame {fuel : Nat} {cs : List Component}
    (pre : ExtractPre initial boundary salt ikm) (frame : Frame initial s boundary)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (noMem : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (rsp : .reg 4 ∉ cs) (mxcsr : .mxcsr ∉ cs) (fcw : .fcw ∉ cs) (df : .df ∉ cs) :
    Frame initial t boundary := by
  have memory := agrees.external noMem
  exact {
    toRunning := frame.toRunning.of_agrees run ready agrees
      (fun c hc a ha => (noMem c hc a ha).elim) (stackAvoid pre) df
    rsp := (agrees.read (n := 64) rsp).trans frame.rsp
    outputPtr := by rw [memory]; exact frame.outputPtr
    registers := by rw [memory]; exact frame.registers
    returnAddress := by rw [memory]; exact frame.returnAddress
    mxcsr := (agrees.mxcsr mxcsr).trans frame.mxcsr
    fcw := (agrees.fcw fcw).trans frame.fcw }

omit [Bindings] in
theorem unchangedSlice {p : BitVec 64} {offset length changed : Nat}
    (same : ∀ a : BitVec 64, a ≠ p + BitVec.ofNat 64 changed → t.external[a]? = s.external[a]?)
    (bound : offset + length ≤ 2^64) (changedBound : changed < 2^64)
    (apart : offset + length ≤ changed ∨ changed < offset) :
    (Component.mem (p + BitVec.ofNat 64 offset) length).Agrees s t := by
  intro i hi
  apply same
  intro h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
  have canceled : BitVec.ofNat 64 (offset + i) = BitVec.ofNat 64 changed := by bv_omega
  have eq := congrArg BitVec.toNat canceled
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset + i < 2^64 by omega),
    Nat.mod_eq_of_lt changedBound] at eq
  omega

end Hkdf.Proofs.NewExpand.Extract.Update
