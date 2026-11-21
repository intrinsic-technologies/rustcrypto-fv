import Sha2.Proofs.Wrapper512.Dispatch.Store
import Sha2.Proofs.Common.Machine.ExecutionState
import Sha2.Proofs.Common.Machine.FrameMemory

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512

theorem initialize512_pre [Bindings] {v : Variant} {initial s : RamState} {data : ByteArray}
    (call : OneShot.ValidCall (v.routine .digest) initial data)
    (state : ExecutionState initial s
      #v[OneShot.outputRegion (v.routine .digest) initial, Stack.region initial 1152])
    (rsp : rspOf s = stackPtr initial - 600)
    (rip : s.RIP = v.pc 0x1a .digest) : Dispatch.Store.Pre v s .digest := by
  have stack : Stack.Valid initial 1152 := call.stack
  have avoid : (Stack.region initial 1152).Avoids
      (fun a => InProgram a ∨ InPageTables a) :=
    (call.separation.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  have bounds (slot : Nat × Nat) (mem : slot ∈ Dispatch.Store.slots .digest) :
      slot.1 + slot.2 ≤ 600 ∧ 0 < slot.2 := by
    have checked : (Dispatch.Store.slots .digest).all
        (fun slot => decide (slot.1 + slot.2 ≤ 600 ∧ 0 < slot.2)) = true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp checked slot mem)
  refine ⟨rip, ?_, ?_⟩
  · intro slot mem
    rw [rsp]
    exact stack_frame_writable stack (by decide) (fun a ha h => avoid a ha (.inr h))
      state.allocated (bounds slot mem).1 (bounds slot mem).2
  · intro slot mem offset len bound
    rw [rsp]
    apply stack_frame_codeApart stack (by decide) (fun a ha h => avoid a ha (.inl h))
      (bounds slot mem).1
    intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (offset + j) (by omega)

end Sha2.Proofs.Digest
