import Sha2.Proofs.Common.Machine.Entry
import Sha2.Proofs.Common.Memory.LoadBytes
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
open X86.UserProcess X86Proofs

theorem stack_valid_bounds {s : RamState} {reserve : Nat} (stack : Stack.Valid s reserve) :
    reserve ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 := by
  refine ⟨stack.2.2.1, ?_⟩
  have bound := stack.1
  change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32 at bound
  rwa [stack_region_end] at bound

theorem stack_valid_sub_toNat {s : RamState} {reserve offset : Nat}
    (stack : Stack.Valid s reserve) (low : offset ≤ reserve) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
  have bounds := stack_valid_bounds stack
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem stack_valid_sub_readable {s : RamState} {reserve offset len : Nat}
    (stack : Stack.Valid s reserve) (low : offset ≤ reserve) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  apply memoryRegion_memReadable stack.1 stack.2.1
  · rw [stack_valid_sub_toNat stack low]
    change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_valid_sub_toNat stack low]
    have bounds := stack_valid_bounds stack
    omega

theorem stack_valid_sub_writable {s : RamState} {reserve offset len : Nat}
    (stack : Stack.Valid s reserve)
    (avoids : (Stack.region s reserve).Avoids InPageTables)
    (low : offset ≤ reserve) (high : len ≤ offset + 8) (positive : 0 < len) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  have read := stack_valid_sub_readable stack low high
  refine MemWritable.of_not_reserved positive read.low read.mem ?_
  intro i hi reserved
  apply avoids (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ reserved
  apply memoryRegion_contains_add stack.1 (len := len) _ _ hi
  · rw [stack_valid_sub_toNat stack low]
    change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_valid_sub_toNat stack low]
    have bounds := stack_valid_bounds stack
    omega

theorem valid_return_boundary [bindings : Bindings] {s : RamState} {reserve : Nat}
    (machine : SupportedMachine bindings s) (stack : Stack.Valid s reserve)
    (address : ValidReturnAddress s) :
    nearReturn64Boundary s = .ok (returnBoundary s) ∧
      (returnBoundary s).rip.toNat < 2^32 ∧ ¬ InProgram (returnBoundary s).rip := by
  have read := stack_valid_sub_readable stack (offset := 0) (len := 8)
    (Nat.zero_le _) (by decide)
  simp only [BitVec.sub_zero] at read
  have near := nearReturn64Boundary_eq s (supportedMachine_readyToStep machine).dataReady
    machine.supported.integer.ss read
  obtain ⟨target, loaded, low, outside⟩ := address
  have value : memLoad s.external (stackPtr s) 64 = target := by
    rw [stackPtr_eq_regValue_rsp]
    apply Sha2.Proofs.Common.Memory.memLoad_of_loadBytes64
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded.2
  refine ⟨near, ?_, ?_⟩
  · change (memLoad s.external (stackPtr s) 64).toNat < 2^32
    rw [value]
    exact low
  · change ¬ InProgram (memLoad s.external (stackPtr s) 64)
    rw [value]
    exact outside

end Sha2.Proofs.Common.Machine
