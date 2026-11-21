import P256.Proofs.Signing.Wrapper.Hash.Frame
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Call

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def layout : StackCallLayout 5112 32 65 4584 :=
  ⟨528, 152, 456, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem core_pre [Bindings] {initial start entry : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Frame initial start entry 528)
    (rip : entry.RIP = 0x10c9c0)
    (input : entry.regValue .rsi = stackPtr initial - 152)
    (output : entry.regValue .rdi = stackPtr initial - 456)
    (digest : entry.regValue .rdx = stackPtr initial - 520)
    (length : entry.regValue .rcx = 32)
    (entropy : entry.regValue .r8 = 1) (empty : entry.regValue .r9 = 0)
    (ret : InProgram (returnBoundary entry).rip) : SignPre entry (returnBoundary initial) := by
  have bounds := stack_bounds (stack pre.context)
  have sp : (stackPtr entry).toNat = (stackPtr initial).toNat - 528 := by
    rw [state.rsp]
    exact stack_sub_toNat (stack pre.context) (by decide)
  have dp : (entry.regValue .rdx).toNat = (stackPtr initial).toNat - 520 := by
    rw [digest]
    exact stack_sub_toNat (stack pre.context) (by decide)
  have op : (entry.regValue .rdi).toNat = (stackPtr initial).toNat - 456 := by
    rw [output]
    exact stack_sub_toNat (stack pre.context) (by decide)
  refine {
    toCalleePre := CalleePre.of_stack_region (stack pre.context) (stack_avoids pre.context)
      (outside pre.context) layout
      state.bindingsSupported state.machine state.directionFlag state.loaded state.allocated
      rip state.rsp input output ret
    digestLength := length
    entropyPointer := entropy
    entropyLength := empty
    digestBounded := ?_
    digestAllocated := ?_
    digestOutput := ?_
    digestStack := ?_
  }
  · change (entry.regValue .rdx).toNat + 32 < 2^32
    rw [dp]
    omega
  · intro a ha
    apply Option.isSome_iff_exists.mp (state.allocated a _)
    apply Option.isSome_iff_exists.mpr ((stack pre.context).2.1 a _)
    change (entry.regValue .rdx).toNat ≤ a.toNat ∧
      a.toNat < (entry.regValue .rdx).toNat + 32 at ha
    rw [dp] at ha
    change (stackPtr initial).toNat - 5112 ≤ a.toNat ∧
      a.toNat < (Stack.region initial 5112).start + (Stack.region initial 5112).size
    rw [stack_region_end]
    constructor <;> omega
  · intro a ha hb
    change (entry.regValue .rdx).toNat ≤ a ∧ a < (entry.regValue .rdx).toNat + 32 at ha
    change (entry.regValue .rdi).toNat ≤ a ∧ a < (entry.regValue .rdi).toNat + 65 at hb
    rw [dp] at ha
    rw [op] at hb
    omega
  · intro a ha hb
    change (entry.regValue .rdx).toNat ≤ a ∧ a < (entry.regValue .rdx).toNat + 32 at ha
    rw [dp] at ha
    change (stackPtr entry).toNat - 4584 ≤ a ∧
      a < (Stack.region entry 4584).start + (Stack.region entry 4584).size at hb
    rw [stack_region_end, sp] at hb
    omega

end P256.Proofs.Signing.Wrapper.Hash.Call
