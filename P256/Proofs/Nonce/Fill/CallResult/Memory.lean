import P256.Proofs.Nonce.Fill.Call

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s called t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

def callRegions (initial : RamState) : Vector MemoryRegion 2 :=
  #v[MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64,
    MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864]

theorem call_region_work (pre : Pre initial boundary orderAddress original)
    {region : MemoryRegion} (member : region ∈ callRegions initial)
    {a : Nat} (inside : region.Contains a) :
    ∃ region ∈ workRegions initial, region.Contains a := by
  have cases : region = MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864 := by
    simpa [callRegions] using member
  rcases cases with rfl | rfl
  · exact ⟨registerRegion initial .rdi 72, by simp [workRegions], drbg_sub pre inside⟩
  · refine ⟨ScalarFrame.workRegion initial 2096, by simp [workRegions], ?_⟩
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (stackPtr initial).toNat - 2096 + 1864 at inside
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (stackPtr initial).toNat - 2096 + 2048
    constructor <;> omega

theorem call_frame_work (pre : Pre initial boundary orderAddress original)
    (memory : MemoryWriteFrame s t (callRegions initial)) :
    MemoryWriteFrame s t (workRegions initial) := by
  intro a ha
  apply memory a
  intro region hr hin
  obtain ⟨region, member, inside⟩ := call_region_work pre hr hin
  exact ha region member inside

theorem call_result_memory (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {entry ret : BitVec 64} {reserve : Nat}
    (capacity : reserve ≤ 1856)
    (effect : (callEffect (fun _ => entry) ret s).Holds s called)
    (pointer : s.regValue .rdi = initial.regValue .rdi + 8)
    (result : CalleeResult called t boundary 64 reserve) :
    MemoryWriteFrame s t (callRegions initial) := by
  have bounds := stack_bounds pre.stack
  have rsp : stackPtr called = stackPtr initial - 240 :=
    effect.writes.1.trans (call_address frame)
  have sp : (stackPtr called).toNat = (stackPtr initial).toNat - 240 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (offset := 240) (by decide)
  have output : called.regValue .rdi = initial.regValue .rdi + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans pointer
  apply memoryWriteFrame_trans (t := called)
  · apply effect.agrees.memoryWriteFrame
    intro c hc a hv
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hv.elim
    · obtain ⟨i, hi, eq⟩ := hv
      rw [call_address frame] at eq
      subst a
      refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864,
        by simp [callRegions], ?_⟩
      have low : (stackPtr initial - 240).toNat = (stackPtr initial).toNat - 240 :=
        stack_sub_toNat pre.stack (offset := 240) (by decide)
      have hn : (stackPtr initial - 240 + BitVec.ofNat 64 i).toNat =
          (stackPtr initial).toNat - 240 + i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          low,
          Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
      change (stackPtr initial).toNat - 2096 ≤ _ ∧
        _ < (stackPtr initial).toNat - 2096 + 1864
      rw [hn]
      constructor <;> omega
    · exact hv.elim
  · intro a ha
    apply result.frame a
    intro region member inside
    have cases : region = registerRegion called .rdi 64 ∨ region = Stack.region called reserve := by
      simpa using member
    rcases cases with rfl | rfl
    · apply ha (MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64)
        (by simp [callRegions])
      simpa only [registerRegion, output] using inside
    · apply ha (MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864)
        (by simp [callRegions])
      change (stackPtr called).toNat - reserve ≤ a.toNat ∧
        a.toNat < (Stack.region called reserve).start + (Stack.region called reserve).size at inside
      rw [stack_region_end, sp] at inside
      change (stackPtr initial).toNat - 2096 ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - 2096 + 1864
      constructor <;> omega

theorem call_frame_read (pre : Pre initial boundary orderAddress original)
    (memory : MemoryWriteFrame s t (callRegions initial))
    {offset n : Nat} (bound : offset ≤ 232) (span : n / 8 ≤ offset + 8) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) n =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) n := by
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr hin
  have cases : region = MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864 := by
    simpa [callRegions] using hr
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [low]; omega), low]
  rcases cases with rfl | rfl
  · exact pre.separation 1 2 (by decide) _ (drbg_sub pre hin)
      (ScalarFrame.stack_contains pre.toCalleePre (by omega) span ⟨i, hi, rfl⟩)
  · change (stackPtr initial).toNat - 2096 ≤ _ ∧
      _ < (stackPtr initial).toNat - 2096 + 1864 at hin
    rw [address] at hin
    omega

theorem Slots.of_call_frame (pre : Pre initial boundary orderAddress original)
    (slots : Slots initial s) (memory : MemoryWriteFrame s t (callRegions initial)) :
    Slots initial t := by
  have read {offset n : Nat} (bound : offset ≤ 232) (span : n / 8 ≤ 232 - offset + 8) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) n =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) n := by
    rw [frameBase_add initial bound]
    exact call_frame_read pre memory (by omega) span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (read (offset := 40) (by decide) (by decide)).trans slots.outputSlot
  · exact (read (offset := 48) (by decide) (by decide)).trans slots.lengthSlot
  · exact (read (offset := 56) (by decide) (by decide)).trans slots.bitsSlot
  · exact (read (offset := 64) (by decide) (by decide)).trans slots.statePointerSlot
  · exact (read (offset := 136) (by decide) (by decide)).trans slots.valuePointerSlot
  · exact (read (offset := 144) (by decide) (by decide)).trans slots.generatorPointerSlot

end P256.Proofs.Nonce.Fill
