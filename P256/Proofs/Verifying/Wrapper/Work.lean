import P256.Spec.Program.Functions
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev workRegion (initial : RamState) := ScalarFrame.Work.region initial 10280 40

theorem work_frame {initial s t : RamState} (stack : Stack.Valid initial 10280)
    (memory : MemoryWriteFrame s t #v[workRegion initial]) :
    MemoryWriteFrame s t (wrapperRegions verifyingKeyVerify initial) := by
  intro a ha
  apply memory a
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  apply ha (callStack verifyingKeyVerify initial) (by simp [wrapperRegions])
  apply stack_contains_callStack
  have bounds := stack_bounds stack
  change (stackPtr initial).toNat-10280 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat-10280+(10280-40) at hin
  change (stackPtr initial).toNat-10280 ≤ a.toNat ∧
    a.toNat < (Stack.region initial 10280).start+(Stack.region initial 10280).size
  rw [stack_region_end]
  constructor <;> omega

theorem work_read {initial s t : RamState} (stack : Stack.Valid initial 10280)
    (memory : MemoryWriteFrame s t #v[workRegion initial]) {offset : Nat} (bound : offset ≤ 40) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0 = _
  rw [memory _]
  · rfl
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  change (stackPtr initial).toNat-10280 ≤ _ ∧
    (stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat <
      (stackPtr initial).toNat-10280+(10280-40) at hin
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,low] at hin
  have small : i < 8 := hi
  omega

end P256.Proofs.Verifying.Wrapper
