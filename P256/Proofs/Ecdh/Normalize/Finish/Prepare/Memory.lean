import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame

theorem local_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) {offset : Nat}
    (bound : offset + 8 ≤ 2056) (align : offset % 8 = 0) :
    MemWritable t (stackPtr t + BitVec.ofNat 64 offset) 8 := by
  rw [scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by omega)]
  exact writable_of_grow (stack_sub_writable8 pre.stack
    (fun a ha h => pre.avoids _ (by simp) a ha (.inr h))
    (by omega) (by omega)) state.allocated

theorem local_byte_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) {offset : Nat} (bound : offset + 1 ≤ 2056) :
    MemWritable t (stackPtr t + BitVec.ofNat 64 offset) 1 := by
  rw [scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by omega)]
  exact writable_of_grow (stack_sub_writable pre.stack
    (fun a ha h => pre.avoids _ (by simp) a ha (.inr h))
    (by omega) (by omega) (by decide)
    (by have h := Nat.mod_lt (stackPtr s - BitVec.ofNat 64 (2056-offset)).toNat
          (by decide : 0 < 4096); omega)) state.allocated

theorem local_work [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ 2008)
    (covered : (Component.mem (stackPtr t + BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s 3464).Contains a.toNat := by
  rw [scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by omega)] at covered
  exact work_contains pre (by omega) (by omega) covered

end P256.Proofs.Ecdh.Normalize.Finish
