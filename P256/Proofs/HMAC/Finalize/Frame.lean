import P256.Proofs.HMAC.Finalize.Interface

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

theorem outer_state_of_scratch_frame [Bindings]
    {initial s t : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (outer : Sha256StateAt s (stackPtr initial - 152#64) message)
    (frame : MemoryWriteFrame s t #v[scratchRegion initial]) :
    Sha256StateAt t (stackPtr initial - 152#64) message := by
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have low := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 152) (by decide)
  refine outer.of_frame ?_ frame ?_
  · change (stackPtr initial - 152#64).toNat + 104 < 2^32
    rw [low]
    omega
  · intro region member
    have eq : region = scratchRegion initial := by simpa using member
    subst region
    intro a ha hb
    change (stackPtr initial - 152#64).toNat ≤ a ∧ a < (stackPtr initial - 152#64).toNat + 104 at ha
    rw [low] at ha
    change (stackPtr initial).toNat - 672 ≤ a ∧ a < (stackPtr initial).toNat - 672 + 520 at hb
    omega

theorem work_memory_frame {initial s t : RamState}
    (memory : MemoryWriteFrame s t #v[workRegion initial 672]) :
    MemoryWriteFrame s t
      #v[registerRegion initial .rdi 0, workRegion initial 672] := by
  intro a ha
  apply memory a
  intro region member
  have eq : region = workRegion initial 672 := by simpa using member
  subst region
  exact ha _ (by simp)

theorem state_of_work_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : HmacStateAt s (initial.regValue .rdi) key input)
    (memory : MemoryWriteFrame s t #v[workRegion initial 672]) :
    HmacStateAt t (initial.regValue .rdi) key input := by
  have stackLow : 672 ≤ (stackPtr initial).toNat := pre.stack.2.2.1
  refine state.of_frame pre.outputBounded memory ?_
  intro region member a ha hb
  have eq : region = workRegion initial 672 := by simpa using member
  subst region
  apply pre.separation 1 2 (by decide) a ha
  change (stackPtr initial).toNat - 672 ≤ a ∧
    a < (stackPtr initial).toNat - 672 + (672 - 48) at hb
  change (stackPtr initial).toNat - 672 ≤ a ∧
    a < (Stack.region initial 672).start + (Stack.region initial 672).size
  rw [stack_region_end]
  exact ⟨hb.1, by omega⟩

theorem local_work_contains [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (rsp : stackPtr s = stackPtr initial - 328#64)
    {offset len : Nat} {a : BitVec 64} (bound : offset + len ≤ 280)
    (covered : (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial 672).Contains a.toNat := by
  rw [stack_address rsp (by omega : offset ≤ 328)] at covered
  exact work_contains pre (by omega) (by omega) covered

end P256.Proofs.HMAC.Finalize
