import Hkdf.Proofs.NewExpand.Expand.Positive.Output
import Hkdf.Proofs.Common.CallFrame.Stack

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

theorem outputChunk_within (entry : RamState) (length n a : Nat)
    (h : (outputChunk entry length n).Contains a) : (registerRegion entry .rcx length).Contains a := by
  rcases h with ⟨lo, hi⟩
  change (entry.regValue .rcx).toNat + 32*n ≤ a at lo
  change a < (entry.regValue .rcx).toNat + 32*n + min (length - 32*n) 32 at hi
  change (entry.regValue .rcx).toNat ≤ a ∧ a < (entry.regValue .rcx).toNat + length
  constructor <;> omega

set_option maxRecDepth 2048 in
theorem copyChunkPre [Bindings] {entry c : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (more : 32*n < length)
    (limit : length ≤ 8160)
    (running : Running entry boundary
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] c)
    (pc : c.RIP = 0x10dd60) (ret : (returnBoundary c).rip = 0x10f548)
    (sp : stackPtr c = stackPtr entry - 544)
    (src : c.regValue .rsi = stackPtr entry - 520)
    (dst : c.regValue .rdi = entry.regValue .rcx + BitVec.ofNat 64 (32*n)) :
    CalleePre c boundary 0x10dd60 (min (length - 32*n) 32) (min (length - 32*n) 32) 0 ∧
    registerRegion c .rdi (min (length - 32*n) 32) = outputChunk entry length n ∧
    Stack.region c 0 = ⟨(stackPtr entry).toNat - 544, 8⟩ := by
  let k := min (length - 32*n) 32
  have stack := pre.call.stack
  have bounds := stack_bounds stack
  have top : (Stack.region entry 2264).start + (Stack.region entry 2264).size =
      (stackPtr entry).toNat + 8 := stack_region_end _ _
  have positive : 0 < length := by omega
  obtain ⟨outBound, outAllocated⟩ := pre.output positive limit
  change (entry.regValue .rcx).toNat + length < 2^32 at outBound
  have outApart : (registerRegion entry .rcx length).Disjoint (Stack.region entry 2264) :=
    (pre.separation positive limit).1 0 1 (by decide)
  have outEq : registerRegion c .rdi k = outputChunk entry length n := by
    unfold registerRegion outputChunk
    rw [dst, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 32*n < 2^64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  have spNat : (stackPtr c).toNat = (stackPtr entry).toNat - 544 := by
    rw [sp]
    exact stack_sub_toNat stack (offset := 544) (by decide)
  have srcNat : (c.regValue .rsi).toNat = (stackPtr entry).toNat - 520 := by
    rw [src]
    exact stack_sub_toNat stack (offset := 520) (by decide)
  have stEq : Stack.region c 0 = ⟨(stackPtr entry).toNat - 544, 8⟩ := by
    change (⟨(stackPtr c).toNat - 0, (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 0)⟩ : MemoryRegion) = _
    rw [spNat, Nat.sub_zero]
    rw [Nat.add_sub_cancel_left]
  have sourceWithin (a : Nat) (ha : (registerRegion c .rsi k).Contains a) :
      (Stack.region entry 2264).Contains a := by
    change (c.regValue .rsi).toNat ≤ a ∧ a < (c.regValue .rsi).toNat + k at ha
    rw [srcNat] at ha
    unfold MemoryRegion.Contains
    rw [top]
    change (stackPtr entry).toNat - 2264 ≤ a ∧ _
    dsimp only [k] at ha
    constructor <;> omega
  have stackWithin (a : Nat) (ha : (Stack.region c 0).Contains a) :
      (Stack.region entry 2264).Contains a := by
    rw [stEq] at ha
    change (stackPtr entry).toNat - 544 ≤ a ∧ a < (stackPtr entry).toNat - 544 + 8 at ha
    unfold MemoryRegion.Contains
    rw [top]
    change (stackPtr entry).toNat - 2264 ≤ a ∧ _
    constructor <;> omega
  have sourceApart : (registerRegion c .rsi k).Disjoint (Stack.region c 0) := by
    intro a hs ht
    have lower := hs.1
    change (c.regValue .rsi).toNat ≤ a at lower
    rw [srcNat] at lower
    rw [stEq] at ht
    have high : a < (stackPtr entry).toNat - 544 + 8 := ht.2
    omega
  have outWithin (a : Nat) (ha : (registerRegion c .rdi k).Contains a) :=
    outputChunk_within entry length n a (outEq ▸ ha)
  have subAlloc (r : MemoryRegion) (within : ∀ a, r.Contains a → (Stack.region entry 2264).Contains a) :
      r.Allocated c.external := fun a ha =>
    Option.isSome_iff_exists.mp (running.allocated _ (Option.isSome_iff_exists.mpr (stack.2.1 _ (within _ ha))))
  refine ⟨{
    stride := pre.call.stride
    machine := running.machine
    directionFlag := running.directionFlag
    loaded := running.loaded
    rip := pc
    inputBounded := ?_
    inputAllocated := subAlloc _ sourceWithin
    outputBounded := ?_
    outputAllocated := fun a ha => Option.isSome_iff_exists.mp (running.allocated _
      (Option.isSome_iff_exists.mpr (outAllocated a (outWithin _ ha))))
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.call.outerBoundary
    returnInProgram := ret ▸ inProgram_of_textOffset 0xf548 (by decide)
    }, outEq, stEq⟩
  · change (c.regValue .rsi).toNat + min _ 32 < 2^32
    rw [srcNat]
    omega
  · rw [outEq]
    change (entry.regValue .rcx).toNat + 32*n + min _ 32 < 2^32
    omega
  · refine ⟨?_, subAlloc _ stackWithin, Nat.zero_le _, ?_⟩
    · rw [stEq]
      change (stackPtr entry).toNat - 544 + 8 < 2^32
      omega
    · change (stackPtr c).toNat % 16 = 8
      rw [spNat]
      have ha : (stackPtr entry).toNat % 16 = 8 := stack.2.2.2
      omega
  · intro i j hij
    rcases (by omega : i.val = 0 ∧ j.val = 1 ∨ i.val = 0 ∧ j.val = 2 ∨ i.val = 1 ∧ j.val = 2) with
      ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals
      have ie := Fin.ext (n := 3) (b := ⟨_, hi ▸ i.isLt⟩) hi
      have je := Fin.ext (n := 3) (b := ⟨_, hj ▸ j.isLt⟩) hj
      rw [ie, je]
    · exact fun a hs ho => outApart a (outWithin _ ho) (sourceWithin _ hs)
    · exact sourceApart
    · exact fun a ho hs => outApart a (outWithin _ ho) (stackWithin _ hs)
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact fun a ha => ((pre.separation positive limit).2 (registerRegion entry .rcx length)
        (by simp)).2 a (outWithin _ ha)
    · exact fun a ha => pre.call.stackAvoid a (stackWithin _ ha)

end Hkdf.Proofs.NewExpand.Expand
