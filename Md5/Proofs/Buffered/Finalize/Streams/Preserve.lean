import Md5.Proofs.Buffered.Update.Calls
import X86Proofs.Program.ReadWrite.Bytes

namespace Md5.Proofs.Buffered.Finalize.Streams

open X86 X86.Machine X86.UserProcess X86Proofs

theorem call_preserves_bytes [Bindings] {boundary : ReturnBoundary} {ret base : BitVec 64}
    {s t : RamState} {len : Nat} {bytes : Nat → UInt8}
    (h : CallSiteResult boundary ret s t) (hb : Bytes s.external base len bytes)
    (hd : RangeApart base len (rdi.read s) (MemoryRoutines.rdx.read s).toNat)
    (hs : RangeApart base len (pushAddr s) 8) : Bytes t.external base len bytes := by
  apply hb.of_agreesExcept h.agrees
  intro i hi c hc hcover
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨j, hj, he⟩ := hcover
    exact hd i hi j hj he
  · obtain ⟨j, hj, he⟩ := hcover
    exact hs i hi j hj he

end Md5.Proofs.Buffered.Finalize.Streams
