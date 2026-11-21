import P256.Proofs.HMAC.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.HMAC.Key.Frame

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

theorem stackPre [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) :
    CalleePre s boundary entry 32 0 reserve := by
  refine { pre.toCalleePre with
    outputBounded := ?_
    outputAllocated := ?_
    separation := ?_
    avoids := ?_ }
  · have h := pre.outputBounded
    change (s.regValue .rdi).toNat + stateBytes < 2^32 at h
    change (s.regValue .rdi).toNat + 0 < 2^32
    omega
  · intro a ha
    exact False.elim (by change _ ≤ _ ∧ _ < _ + 0 at ha; omega)
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro a _ hb; change _ ≤ _ ∧ _ < _ + 0 at hb; omega
    · exact pre.separation 0 2 (by decide)
    · intro a ha _; change _ ≤ _ ∧ _ < _ + 0 at ha; omega
  · intro region hr a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact False.elim (by change _ ≤ _ ∧ _ < _ + 0 at ha; omega)
    · exact pre.avoids _ (by simp) a ha

theorem stack_address {s t : RamState} {depth : Nat}
    (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 depth)
    {offset : Nat} (h : offset ≤ depth) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (depth-offset) := by
  have hn : depth = (depth - offset) + offset := by omega
  rw [hsp, hn, BitVec.ofNat_add]
  rw [← BitVec.sub_sub, BitVec.sub_add_cancel, Nat.add_sub_cancel]

theorem work_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {stateBytes reserve : Nat}
    (pre : HashCalleePre s boundary entry stateBytes reserve) {offset len : Nat} {a : BitVec 64}
    (ho : offset ≤ reserve) (hl : len + 48 ≤ offset)
    (covered : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s reserve).Contains a.toNat := ScalarFrame.work_contains pre.toCalleePre ho hl covered


theorem after_result [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {stateBytes reserve outputBytes callReserve : Nat}
    {stackOffset nextOffset : BitVec 64}
    (pre : HashCalleePre s boundary entry stateBytes reserve) (hreserve : 48 ≤ reserve)
    (state : ScalarFrame.FrameState s t 0 reserve stackOffset)
    (result : CalleeResult t u boundary outputBytes callReserve)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 0, workRegion s reserve])
    (rsp : stackPtr u = stackPtr s - nextOffset) :
    ScalarFrame.FrameState s u 0 reserve nextOffset := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (ScalarFrame.output_work_frame (stackPre pre) memory),
    rsp, ?_, ?_, result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.output_work_read (stackPre pre) hreserve memory bound (by omega)).trans
      (state.saved entry he)
  · have h := ScalarFrame.output_work_read (stackPre pre) hreserve memory (offset := 0)
      (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.HMAC.Finalize
