import Md5.Proofs.Buffered.FinalizeReset.Export.Execution.Blocks
import Md5.Proofs.Buffered.FinalizeReset.Frame

namespace Md5.Proofs.Buffered.FinalizeReset.Export

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

attribute [local x86_compose] stackPtr_eq_read

theorem resetEffect_local {variant : Variant} : Effect.Local (fun s ↦ resetEffect s variant) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ hi ↦ congrArg some hi, fun _ ↦ ?_⟩
  · simp only [resetEffect, stackPtr_eq_read, h.read_reg]
  · simp [resetEffect, Write.Full, Operand.Full]

private theorem copyEffect_writes {variant : Variant} {s t : RamState} (h : Obs s t) :
    (copyEffect s variant).writes = (copyEffect t variant).writes := by
  simp only [copyEffect, outputAddress, stackPtr_eq_read, h.read_reg, h.read_mem]

private theorem copyEffect_full (variant : Variant) (s : RamState) :
    ∀ w ∈ (copyEffect s variant).writes, w.Full := by
  intro w hw
  simp only [copyEffect, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals simp [Write.Full, Operand.Full]

set_option maxHeartbeats 800000 in
theorem copyEffect_local {variant : Variant} : Effect.Local (fun s ↦ copyEffect s variant) :=
  ⟨fun _ _ _ ↦ rfl, fun _ _ h ↦ copyEffect_writes (variant := variant) h,
    fun _ _ _ ↦ rfl, fun _ _ _ _ hi ↦ congrArg some hi, copyEffect_full variant⟩

theorem save_storage {s t : RamState} (hs : Storage s) (h : (saveEffect s).Holds s t) :
    Storage t := by
  have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
    (by x86_norm [saveEffect])
  apply hs.of_agrees h.agrees hsp
  unfold outputAddress
  rw [hsp, ← (h.obsAfter (by simp [saveEffect, Write.Full, Operand.Full]) true).read_mem]
  x86_norm [saveEffect]

theorem reset_storage {variant : Variant} {s t : RamState} (hs : Storage s variant) (h : (resetEffect s variant).Holds s t) :
    Storage t variant := by
  have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
    (by x86_norm [resetEffect])
  apply hs.of_agrees h.agrees hsp
  unfold outputAddress
  rw [hsp, ← (h.obsAfter (by simp [resetEffect, Write.Full, Operand.Full]) true).read_mem]
  x86_norm [resetEffect]

theorem memLoad_outputStore_stack {variant : Variant} {s : RamState} (h : Storage s variant) (m : Ram)
    (outOffset stackOffset : BitVec 64) {k : Nat} (v : BitVec 64)
    (ho : outOffset.toNat + 8 ≤ 16) (hs : stackOffset.toNat + k / 8 ≤ variant.stackBytes) :
    memLoad (memStore m (outputAddress s + outOffset) v) (stackPtr s + stackOffset) k =
      memLoad m (stackPtr s + stackOffset) k := by
  apply memLoad_memStore_rangeApart
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    outputStackApart h outOffset.toNat 8 stackOffset.toNat (k / 8) ho hs

theorem memLoad_outputStore_stack_zero {variant : Variant} {s : RamState} (h : Storage s variant) (m : Ram)
    (stackOffset : BitVec 64) {k : Nat} (v : BitVec 64)
    (hs : stackOffset.toNat + k / 8 ≤ variant.stackBytes) :
    memLoad (memStore m (outputAddress s) v) (stackPtr s + stackOffset) k =
      memLoad m (stackPtr s + stackOffset) k := by
  apply memLoad_memStore_rangeApart
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero] using
    outputStackApart h 0 8 stackOffset.toNat (k / 8) (by decide) hs

theorem composed_effect {s t : RamState} (hs : Storage s)
    (h : (Effect.seq (Effect.seq saveEffect resetEffect) copyEffect s).Holds s t) :
    (effect s).Holds s t := by
  have hmem := memLoad_outputStore_stack hs
  have hzero := memLoad_outputStore_stack_zero hs
  x86_norm [outputAddress] at hmem hzero
  apply h.weaken
  · x86_norm [saveEffect, resetEffect, copyEffect, effect]
  · x86_norm [saveEffect, resetEffect, copyEffect, effect,
      hmem, hzero, outputAddress, BitVec.add_zero]
    repeat constructor
  · intro i; cases i <;> x86_norm [saveEffect, resetEffect, copyEffect, effect]
  · x86_norm [saveEffect, resetEffect, copyEffect, effect, outputAddress, BitVec.add_zero]

theorem copy_storage {variant : Variant} {s t : RamState} (hs : Storage s variant)
    (h : (copyEffect s variant).Holds s t) : Storage t variant := by
  have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
    (by x86_norm [copyEffect])
  have hmem := memLoad_outputStore_stack hs
  have hzero := memLoad_outputStore_stack_zero hs
  x86_norm [outputAddress] at hmem hzero
  apply hs.of_agrees h.agrees hsp
  unfold outputAddress
  rw [hsp, ← (h.obsAfter (by simp [copyEffect, Write.Full, Operand.Full]) true).read_mem]
  cases variant <;> x86_norm [copyEffect, outputAddress, hmem, hzero]

theorem memLoad_stackStore_output {variant : Variant} {s : RamState}
    (h : Storage s variant) (m : Ram) (stackOffset outOffset : BitVec 64)
    {n k : Nat} (v : BitVec n)
    (hs : stackOffset.toNat + n / 8 ≤ variant.stackBytes)
    (ho : outOffset.toNat + k / 8 ≤ 16) :
    memLoad (memStore m (stackPtr s + stackOffset) v) (outputAddress s + outOffset) k =
      memLoad m (outputAddress s + outOffset) k := by
  apply memLoad_memStore_rangeApart
  have hh := outputStackApart h outOffset.toNat (k / 8) stackOffset.toNat (n / 8) ho hs
  intro i hi j hj he
  apply hh j hj i hi
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he.symm

theorem memLoad_stackStore_output_zero {variant : Variant} {s : RamState}
    (h : Storage s variant) (m : Ram) (stackOffset : BitVec 64)
    {n k : Nat} (v : BitVec n)
    (hs : stackOffset.toNat + n / 8 ≤ variant.stackBytes) (ho : k / 8 ≤ 16) :
    memLoad (memStore m (stackPtr s + stackOffset) v) (outputAddress s) k =
      memLoad m (outputAddress s) k := by
  apply memLoad_memStore_rangeApart
  have hh := outputStackApart h 0 (k / 8) stackOffset.toNat (n / 8) (by simpa only [Nat.zero_add] using ho) hs
  intro i hi j hj he
  apply hh j hj i hi
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero] using he.symm

set_option maxHeartbeats 500000 in
theorem direct_composed_effect {s t : RamState} (hs : Storage s .direct)
    (h : (Effect.seq (fun s ↦ copyEffect s .direct)
      (fun s ↦ resetEffect s .direct) s).Holds s t) :
    (effect s .direct).Holds s t := by
  have hmem := memLoad_outputStore_stack hs
  have hzero := memLoad_outputStore_stack_zero hs
  x86_norm [outputAddress] at hmem hzero
  have hstack := memLoad_stackStore_output hs
  have hstackzero := memLoad_stackStore_output_zero hs
  x86_norm [outputAddress] at hstack hstackzero
  apply h.weaken
  · x86_norm [resetEffect, copyEffect, effect]
  · x86_norm [resetEffect, copyEffect, effect,
      hmem, hzero, hstack, hstackzero, outputAddress, BitVec.add_zero]
    repeat constructor
  · intro i; cases i <;> x86_norm [resetEffect, copyEffect, effect]
  · x86_norm [resetEffect, copyEffect, effect, outputAddress, BitVec.add_zero]

end Md5.Proofs.Buffered.FinalizeReset.Export
