import P256.Proofs.ReadBe.Memory
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

open P256.Proofs.Program P256.Proofs.Common.Machine

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

def scratchRegion (s : RamState) : MemoryRegion := ⟨(stackPtr s).toNat - 80, 32⟩

theorem Pre.scratch_subset (pre : Pre s boundary) {a : Nat}
    (ha : (scratchRegion s).Contains a) : (Stack.region s 128).Contains a := by
  change (stackPtr s).toNat - 80 ≤ a ∧ a < (stackPtr s).toNat - 80 + 32 at ha
  change (stackPtr s).toNat - 128 ≤ a ∧ a < (Stack.region s 128).start + (Stack.region s 128).size
  rw [stack_region_end]
  have := (stack_bounds pre.stack)
  constructor <;> omega

theorem Pre.scratch_contains (pre : Pre s boundary) {offset i len : Nat}
    (hoffset : offset ≤ 80) (hstart : 48 ≤ offset) (hlen : len ≤ offset - 48)
    (hi : i < len) : (scratchRegion s).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  have hs := (stack_bounds pre.stack)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2^64), stack_sub_toNat pre.stack (by omega),
    Nat.mod_eq_of_lt (by omega)]
  change (stackPtr s).toNat - 80 ≤ _ ∧ _ < (stackPtr s).toNat - 80 + 32
  constructor <;> omega

theorem Pre.loaded_of_frame (pre : Pre s boundary)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdx 32, Stack.region s 128]) :
    ProgramLoaded t := by
  intro a b hf
  rw [frame a]
  · exact pre.loaded a b hf
  · intro region hr hin
    exact pre.avoids region (by simpa using hr) a hin (.inl ⟨b, hf⟩)

theorem Pre.local_frame (pre : Pre s boundary)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdx 32, scratchRegion s]) :
    MemoryWriteFrame t u #v[registerRegion s .rdx 32, Stack.region s 128] := by
  intro a ha
  apply frame a
  intro r hr hin
  have hr' : r = registerRegion s .rdx 32 ∨ r = scratchRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ha _ (by simp) hin
  · exact ha _ (by simp) (pre.scratch_subset hin)

theorem Pre.saved_word_preserved (pre : Pre s boundary)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdx 32, scratchRegion s])
    {offset : Nat} (hoffset : offset ≤ 48) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?.getD 0 =
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?.getD 0
  congr 1
  apply frame
  intro r hr ha
  have hr' : r = registerRegion s .rdx 32 ∨ r = scratchRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ha
      (pre.stack_contains (by omega) (len := 8) (by omega) hi)
  · have hb := (stack_bounds pre.stack)
    change (stackPtr s).toNat - 80 ≤ _ ∧ _ < (stackPtr s).toNat - 80 + 32 at ha
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      stack_sub_toNat pre.stack (by omega), Nat.mod_eq_of_lt (by omega)] at ha
    omega

theorem Frame.of_agrees {cs : List Component} (pre : Pre s boundary) (frame : Frame s t)
    (ready : ReadyToStep u) (agree : AgreesExcept cs t u)
    (rsp : stackPtr u = frameBase s)
    (writes : WritesWithin cs #v[registerRegion s .rdx 32, scratchRegion s])
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Frame s u := by
  have localFrame := agree.memoryWriteFrame writes
  have total := memoryWriteFrame_trans frame.frame (pre.local_frame localFrame)
  refine ⟨rsp, bindingsSupported_of_ready_agrees frame.bindingsSupported ready agree,
    supportedMachine_of_ready_agrees frame.machine ready agree,
    agree.directionFlagClear (by component_not_mem) frame.directionFlag,
    (agree.mxcsr (by component_not_mem)).trans frame.mxcsr,
    (agree.fcw (by component_not_mem)).trans frame.fp87,
    total, pre.loaded_of_frame total, fun a ha => agree.grow a (frame.allocated a ha), ?_, ?_⟩
  · have h := pre.saved_word_preserved localFrame (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress
  · intro i hi
    exact (pre.saved_word_preserved localFrame (offset := 8*(i+1)) (by omega)).trans (frame.saved i hi)

end P256.Proofs.ReadBe
