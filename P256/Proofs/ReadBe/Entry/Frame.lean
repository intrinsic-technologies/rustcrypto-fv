import P256.Proofs.ReadBe.Memory
import P256.Proofs.ReadBe.Entry.Prologue
import P256.Proofs.Common.Field.SquareRoot.Multiply.Prologue
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

open P256.Proofs.Program P256.Proofs.Common.Machine

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}

def entryComponents (s : RamState) : List Component :=
  [.reg 0, .reg 2, .reg 3, .reg 4, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .mem (stackPtr s - 24) 8, .mem (stackPtr s - 32) 8,
    .mem (stackPtr s - 40) 8, .mem (stackPtr s - 48) 8, .mem (stackPtr s - 64) 8]

theorem entry_writes (pre : Pre s boundary) :
    WritesWithin (entryComponents s) #v[registerRegion s .rdx 32, Stack.region s 128] := by
  intro c hc a ha
  refine ⟨Stack.region s 128, by simp, ?_⟩
  simp only [entryComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  all_goals
    obtain ⟨i, hi, rfl⟩ := ha
    exact pre.stack_contains (by decide +kernel) (by decide +kernel) hi

def entryMemory (s : RamState) : Ram :=
  memStore (P256.Proofs.Program.saveMemory s) (stackPtr s - 64) (4 : BitVec 64)

omit bindings in
theorem entryMemory_saved (s : RamState) :
    ∀ i < 6, memLoad (entryMemory s)
      (stackPtr s - BitVec.ofNat 64 (8 * (i + 1))) 64 = s.regValue ReadBe.savedRegisters[i]! := by
  intro i hi
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [entryMemory, BitVec.sub_eq_add_neg, ReadBe.savedRegisters, List.getElem!_cons_zero, List.getElem!_cons_succ]
    rw [memLoad_memStore_apart _ (stackPtr s) _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)]
  · simpa only [BitVec.sub_eq_add_neg] using P256.Proofs.Program.saveMemory_saved s (.rbp, 8) (by simp [P256.Proofs.Program.savedRegisters])
  · simpa only [BitVec.sub_eq_add_neg] using P256.Proofs.Program.saveMemory_saved s (.r15, 16) (by simp [P256.Proofs.Program.savedRegisters])
  · simpa only [BitVec.sub_eq_add_neg] using P256.Proofs.Program.saveMemory_saved s (.r14, 24) (by simp [P256.Proofs.Program.savedRegisters])
  · simpa only [BitVec.sub_eq_add_neg] using P256.Proofs.Program.saveMemory_saved s (.r13, 32) (by simp [P256.Proofs.Program.savedRegisters])
  · simpa only [BitVec.sub_eq_add_neg] using P256.Proofs.Program.saveMemory_saved s (.r12, 40) (by simp [P256.Proofs.Program.savedRegisters])
  · simpa only [BitVec.sub_eq_add_neg] using P256.Proofs.Program.saveMemory_saved s (.rbx, 48) (by simp [P256.Proofs.Program.savedRegisters])

omit bindings in
theorem entryMemory_return (s : RamState) :
    memLoad (entryMemory s) (stackPtr s) 64 = (returnBoundary s).rip := by
  simp only [entryMemory, BitVec.sub_eq_add_neg]
  rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)]
  exact P256.Proofs.Common.Field.SquareRoot.Multiply.savedMemory_return s

theorem frame_correct (pre : Pre s boundary) (ready : ReadyToStep t)
    (loaded : ProgramLoaded t) (rsp : stackPtr t = frameBase s)
    (memory : t.external = entryMemory s)
    (agrees : AgreesExcept (entryComponents s) s t) : Frame s t := by
  refine ⟨rsp, bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    P256.Proofs.Program.supportedMachine_of_ready_agrees pre.machine ready agrees,
    agrees.directionFlagClear (by component_not_mem) pre.directionFlag, agrees.mxcsr (by component_not_mem),
    agrees.fcw (by component_not_mem), agrees.memoryWriteFrame (entry_writes pre),
    loaded, agrees.grow, ?_, ?_⟩
  · rw [memory]
    exact entryMemory_return s
  · rw [memory]
    exact entryMemory_saved s

theorem inputBytes_preserved (pre : Pre s boundary) (frame : Frame s t)
    {input : ByteArray} (bytes : (registerRegion s .rdi 32).HasBytes s.external input) :
    (registerRegion s .rdi 32).HasBytes t.external input := by
  refine ⟨bytes.1, ?_⟩
  intro i
  have offset : BitVec.ofNat 64 ((registerRegion s .rdi 32).start + i.val) =
      s.regValue .rdi + BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add]
    simp only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [offset, pre.input_preserved frame.frame (by have := i.isLt; have := bytes.1; change input.size = 32 at this; omega)]
  simpa only [offset] using bytes.2 i

end P256.Proofs.ReadBe.Entry
