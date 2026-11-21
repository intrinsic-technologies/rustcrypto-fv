import P256.Proofs.Nonce.Fill.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {state : State}

def workRegions (initial : RamState) : Vector MemoryRegion 3 :=
  #v[registerRegion initial .rdi 72, registerRegion initial .rsi 32,
    ScalarFrame.workRegion initial 2096]

theorem work_substack (pre : Pre initial boundary orderAddress state) {a : Nat}
    (inside : (ScalarFrame.workRegion initial 2096).Contains a) :
    (Stack.region initial 2096).Contains a := by
  change (stackPtr initial).toNat - 2096 ≤ a ∧
    a < (stackPtr initial).toNat - 2096 + 2048 at inside
  have bounds := stack_bounds pre.stack
  change (stackPtr initial).toNat - 2096 ≤ a ∧
    a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
  rw [stack_region_end]
  constructor <;> omega

theorem work_frame (pre : Pre initial boundary orderAddress state)
    (memory : MemoryWriteFrame s t (workRegions initial)) :
    MemoryWriteFrame s t (regions initial) := by
  intro a ha
  apply memory a
  intro region hr hin
  have cases : region = registerRegion initial .rdi 72 ∨
      region = registerRegion initial .rsi 32 ∨ region = ScalarFrame.workRegion initial 2096 := by
    simpa [workRegions] using hr
  rcases cases with rfl | rfl | rfl
  · exact ha _ (by simp [regions]) hin
  · exact ha _ (by simp [regions]) hin
  · exact ha _ (by simp [regions]) (work_substack pre hin)

theorem work_read (pre : Pre initial boundary orderAddress state)
    (memory : MemoryWriteFrame s t (workRegions initial))
    {offset n : Nat} (bound : offset ≤ 48) (span : n / 8 ≤ offset + 8) :
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
  have cases : region = registerRegion initial .rdi 72 ∨
      region = registerRegion initial .rsi 32 ∨ region = ScalarFrame.workRegion initial 2096 := by
    simpa [workRegions] using hr
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [low]; omega), low]
  have stack : (Stack.region initial 2096).Contains
      (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
    change (stackPtr initial).toNat - 2096 ≤ _ ∧
      _ < (Stack.region initial 2096).start + (Stack.region initial 2096).size
    rw [stack_region_end, address]
    constructor <;> omega
  rcases cases with rfl | rfl | rfl
  · exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin stack
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin stack
  · change (stackPtr initial).toNat - 2096 ≤ _ ∧
      _ < (stackPtr initial).toNat - 2096 + 2048 at hin
    rw [address] at hin
    omega

theorem Frame.after_effect {components : List Component}
    (pre : Pre initial boundary orderAddress state) (input : Frame initial s)
    (ready : ReadyToStep t) (agrees : AgreesExcept components s t)
    (writes : WritesWithin components (workRegions initial)) (sp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Frame initial t := by
  have memory := agrees.memoryWriteFrame writes
  refine ⟨bindingsSupported_of_ready_agrees input.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees input.machine ready agrees, ?_,
    agrees.directionFlagClear hdf input.directionFlag,
    fun a ha => agrees.grow a (input.allocated a ha),
    memoryWriteFrame_trans input.frame (work_frame pre memory),
    (agrees.read (n := 64) (r := 4) sp).trans input.rsp, ?_, ?_,
    (agrees.mxcsr hmxcsr).trans input.mxcsr, (agrees.fcw hfcw).trans input.fp87⟩
  · intro a b hb
    rw [work_frame pre memory a]
    · exact input.loaded a b hb
    · intro region hr hin
      have cases : region = registerRegion initial .rdi 72 ∨
          region = registerRegion initial .rsi 32 ∨ region = Stack.region initial 2096 := by
        simpa [regions] using hr
      rcases cases with rfl | rfl | rfl
      · exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)
      · exact pre.outputAvoids a hin (.inl ⟨b, hb⟩)
      · exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)
  · intro item member
    have bound : item.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (work_read pre memory bound (by omega)).trans (input.saved item member)
  · have h := work_read pre memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans input.returnAddress

end P256.Proofs.Nonce.Fill
