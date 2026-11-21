import P256.Proofs.Nonce.Fill.Generate.Copy.Call
import P256.Proofs.Nonce.Fill.CallResult.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

variable [Bindings] {initial s called t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

def copyRegions (initial : RamState) : Vector MemoryRegion 2 :=
  #v[registerRegion initial .rsi 32, MemoryRegion.mk (stackPtr initial - 240).toNat 8]

theorem call_region_sub (pre : Pre initial boundary orderAddress original) {a : Nat}
    (inside : (MemoryRegion.mk (stackPtr initial - 240).toNat 8).Contains a) :
    (Stack.region initial 2096).Contains a := by
  have bounds := stack_bounds pre.stack
  have low : (stackPtr initial - 240).toNat = (stackPtr initial).toNat - 240 :=
    stack_sub_toNat pre.stack (by decide)
  change (stackPtr initial - 240).toNat ≤ a ∧ a < (stackPtr initial - 240).toNat + 8 at inside
  rw [low] at inside
  change (stackPtr initial).toNat - 2096 ≤ a ∧ a < (Stack.region initial 2096).start + _
  rw [stack_region_end]
  constructor <;> omega

theorem result_memory (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state)
    (effect : (callEffect (fun _ => 0x11c930) 0x1073d2 s).Holds s called)
    (agrees : AgreesExcept (Program.Copy.copyComponents called 32 ++ [.reg 4, .rip]) called t) :
    MemoryWriteFrame s t (copyRegions initial) := by
  have destination : called.regValue .rdi = initial.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.rdi
  apply memoryWriteFrame_trans (t := called)
  · apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [call_address input.toFrame] at ha
    refine ⟨MemoryRegion.mk (stackPtr initial - 240).toNat 8, by simp [copyRegions], ?_⟩
    have bound : (MemoryRegion.mk (stackPtr initial - 240).toNat 8).Bounded := by
      change (stackPtr initial - 240).toNat + 8 < 2^32
      have low : (stackPtr initial - 240).toNat = (stackPtr initial).toNat - 240 :=
        stack_sub_toNat pre.stack (offset := 240) (by decide)
      rw [low]
      have := stack_bounds pre.stack
      omega
    obtain ⟨i, hi, rfl⟩ := ha
    exact memoryRegion_contains_add bound (Nat.le_refl _) (Nat.le_refl _) hi
  · apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [Program.Copy.copyComponents, Program.Copy.registerComponents, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    rw [destination]
    exact ⟨_, by simp [copyRegions], memoryRegion_contains_add pre.inputBounded
      (Nat.le_refl _) (Nat.le_refl _) hi⟩

theorem result_work (pre : Pre initial boundary orderAddress original)
    (memory : MemoryWriteFrame s t (copyRegions initial)) :
    MemoryWriteFrame s t (workRegions initial) := by
  intro a ha
  apply memory a
  intro r hr hin
  have cases : r = registerRegion initial .rsi 32 ∨
      r = MemoryRegion.mk (stackPtr initial - 240).toNat 8 := by simpa [copyRegions] using hr
  rcases cases with rfl | rfl
  · exact ha _ (by simp [workRegions]) hin
  · apply ha (ScalarFrame.workRegion initial 2096) (by simp [workRegions])
    have low : (stackPtr initial - 240).toNat = (stackPtr initial).toNat - 240 :=
      stack_sub_toNat pre.stack (by decide)
    have bounds := stack_bounds pre.stack
    change (stackPtr initial - 240).toNat ≤ a.toNat ∧ a.toNat < (stackPtr initial - 240).toNat + 8 at hin
    rw [low] at hin
    change (stackPtr initial).toNat - 2096 ≤ a.toNat ∧ a.toNat < (stackPtr initial).toNat - 2096 + 2048
    constructor <;> omega

theorem result_slots (pre : Pre initial boundary orderAddress original)
    (slots : Slots initial s) (memory : MemoryWriteFrame s t (copyRegions initial)) : Slots initial t := by
  apply slots.of_stack_reads
  intro off n bound span
  have low := stack_sub_toNat pre.stack (offset := off) (by omega)
  have bounds := stack_bounds pre.stack
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply memory
  intro r hr hin
  have cases : r = registerRegion initial .rsi 32 ∨
      r = MemoryRegion.mk (stackPtr initial - 240).toNat 8 := by simpa [copyRegions] using hr
  rcases cases with rfl | rfl
  · exact pre.separation 0 2 (by decide) _ hin
      (ScalarFrame.stack_contains pre.toCalleePre (by omega) span ⟨i, hi, rfl⟩)
  · have hn : (stackPtr initial - BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - off + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, low,
        Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
    have lo : (stackPtr initial - 240).toNat = (stackPtr initial).toNat - 240 :=
      stack_sub_toNat pre.stack (offset := 240) (by decide)
    change (stackPtr initial - 240).toNat ≤ _ ∧
      _ < (stackPtr initial - 240).toNat + 8 at hin
    rw [lo, hn] at hin
    omega

theorem result_generator (pre : Pre initial boundary orderAddress original)
    (memory : MemoryWriteFrame s t (copyRegions initial))
    (generator : GeneratorAt s (initial.regValue .rdi) orderAddress state) :
    GeneratorAt t (initial.regValue .rdi) orderAddress state := by
  apply generator.of_frame pre.outputBounded pre.orderBounded memory
  · intro r hr a ha hb
    have cases : r = registerRegion initial .rsi 32 ∨
        r = MemoryRegion.mk (stackPtr initial - 240).toNat 8 := by simpa [copyRegions] using hr
    rcases cases with rfl | rfl
    · exact pre.separation 0 1 (by decide) a hb ha
    · exact pre.separation 1 2 (by decide) a ha (call_region_sub pre hb)
  · intro r hr a ha hb
    have cases : r = registerRegion initial .rsi 32 ∨
        r = MemoryRegion.mk (stackPtr initial - 240).toNat 8 := by simpa [copyRegions] using hr
    rcases cases with rfl | rfl
    · exact pre.orderDisjoint _ (by simp) a ha hb
    · exact pre.orderDisjoint _ (by simp) a ha (call_region_sub pre hb)

end P256.Proofs.Nonce.Fill.Generate.Copy
