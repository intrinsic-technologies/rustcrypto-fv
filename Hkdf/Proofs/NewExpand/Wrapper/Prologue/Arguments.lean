import Hkdf.Proofs.NewExpand.Wrapper.Frame

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stackArgumentRead [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (run : Running initial s) (i : Nat) (first : 1 ≤ i) (last : i ≤ 2) :
    MemReadable s (stackPtr initial + BitVec.ofNat 64 (8*i)) 8 ∧
      memLoad s.external (stackPtr initial + BitVec.ofNat 64 (8*i)) 64 = stackArgument initial i := by
  let slot := stackArgumentSlot initial i
  let addr := stackPtr initial + BitVec.ofNat 64 (8*i)
  obtain ⟨bound, allocated⟩ := hCall.stackArgumentsInMemory i (by
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> decide)
  have low : slot.start + 8 < 2^32 := bound
  have start : slot.start = (stackPtr initial).toNat + 8*i := rfl
  have address : BitVec.ofNat 64 slot.start = addr := by
    simp only [start, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, addr]
  have natAddr : addr.toNat = slot.start := by
    rw [← address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have readable : MemReadable initial addr 8 :=
    memoryRegion_memReadable bound allocated (Nat.le_of_eq natAddr.symm) (by rw [natAddr]; exact Nat.le_refl _)
  have same : (Component.mem addr 8).Agrees initial s := by
    apply CallFrame.frame_agrees_of_disjoint run.frame
    · rw [natAddr]; omega
    · intro r hr a ha hs
      obtain rfl := Vector.mem_singleton.mp hr
      have top := hs.2
      rw [stack_region_end] at top
      have bottom := ha.1
      change addr.toNat ≤ a at bottom
      rw [natAddr, start] at bottom
      omega
  refine ⟨⟨readable.low, fun k hk ↦ run.allocated _ (readable.mem k hk)⟩, ?_⟩
  change memLoad s.external addr 64 = _
  rw [CallFrame.agrees_memLoad same]
  have bytes := (Bytes.of_memLoad (n := 64) readable.mem).loadBytes64
  unfold stackArgument
  rw [show BitVec.ofNat 64 (stackArgumentSlot initial i).start = addr from address, bytes]

end Hkdf.Proofs.NewExpand.Wrapper
