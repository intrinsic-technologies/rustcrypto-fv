import P256.Proofs.Verifying.Combination.Table.Memory
import P256.Proofs.Verifying.Combination.Table.Result

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem output_copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (state : FrameState s t cursor 1104) (rip : t.RIP = 0x11c930)
    (src : t.regValue .rsi = stackPtr s - 1088)
    (dst : t.regValue .rdi = s.regValue .rdi) (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary 0x11c930 768 768 128 := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat - 1104 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hin : (t.regValue .rsi).toNat = (stackPtr s).toNat - 1088 := by
    rw [src]
    exact stack_sub_toNat pre.stack (by decide)
  have outputRegion : registerRegion t .rdi 768 = registerRegion s .rdi 768 := by
    simp only [registerRegion, dst]
  have sub (region : MemoryRegion)
      (hstart : (stackPtr s).toNat - 2120 ≤ region.start)
      (hend : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s 2120).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr s).toNat - 2120 ≤ a ∧ a < (Stack.region s 2120).start + (Stack.region s 2120).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub := sub (Stack.region t 128)
    (by change _ ≤ (stackPtr t).toNat - 128; rw [hsp]; omega)
    (by rw [stack_region_end, hsp]; omega)
  have inputSub := sub (registerRegion t .rsi 768)
    (by change _ ≤ (t.regValue .rsi).toNat; rw [hin]; omega)
    (by change (t.regValue .rsi).toNat + 768 ≤ _; rw [hin]; omega)
  have alloc (region : MemoryRegion)
      (hsub : ∀ a, region.Contains a → (Stack.region s 2120).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (hsub a.toNat ha))))
  have apart := pre.separation (1 : Fin 3) 2 (by decide)
  refine {
    bindingsSupported := state.bindingsSupported
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := ?_
    inputAllocated := alloc _ inputSub
    outputBounded := outputRegion ▸ pre.outputBounded
    outputAllocated := ?_
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret
  }
  · change (t.regValue .rsi).toNat + 768 < 2^32
    rw [hin]
    omega
  · rw [outputRegion]
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.outputAllocated a ha)))
  · refine ⟨?_, alloc _ stackSub, ?_, ?_⟩
    · change (Stack.region t 128).start + (Stack.region t 128).size < 2^32
      rw [stack_region_end, hsp]
      omega
    · change 128 ≤ (stackPtr t).toNat
      rw [hsp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [hsp]
      have hm : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro a ha hb
      change (registerRegion t .rdi 768).Contains a at hb
      exact apart a (outputRegion ▸ hb) (inputSub a ha)
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 768 at ha
      change (Stack.region t 128).start ≤ a ∧ a < (Stack.region t 128).start + (Stack.region t 128).size at hb
      rw [hin] at ha
      rw [stack_region_end, hsp] at hb
      omega
    · intro a ha hb
      change (registerRegion t .rdi 768).Contains a at ha
      exact apart a (outputRegion ▸ ha) (stackSub a hb)
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputRegion ▸ ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)

theorem output_copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (state : FrameState s t cursor 1104) (result : CalleeResult t u boundary 768 128)
    (dst : t.regValue .rdi = s.regValue .rdi) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 768, workRegion s] := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat - 1104 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  intro a ha
  apply result.frame a
  intro region hr hin
  have hr' : region = registerRegion t .rdi 768 ∨ region = Stack.region t 128 := by simpa using hr
  rcases hr' with rfl | rfl
  · apply ha (registerRegion s .rdi 768) (by simp)
    simpa only [registerRegion, dst] using hin
  · apply ha (workRegion s) (by simp)
    change (stackPtr t).toNat - 128 ≤ a.toNat ∧ a.toNat < (Stack.region t 128).start + (Stack.region t 128).size at hin
    rw [stack_region_end, hsp] at hin
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 2120 + 2088
    constructor <;> omega

theorem FrameState.after_output_copy [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (state : FrameState s t cursor 1104) (result : CalleeResult t u boundary 768 128)
    (dst : t.regValue .rdi = s.regValue .rdi) : FrameState s u cursor := by
  have memory := output_copy_frame pre state result dst
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre memory), ?_, ?_,
    (result.calleeSaved .rbp (by simp)).trans state.rbp,
    (result.calleeSaved .r13 (by simp)).trans state.r13, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hsp : stackPtr u = stackPtr t + 8 := result.rsp
    rw [hsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 32 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre memory hb (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem output_copy_cursor [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (state : FrameState s t cursor 1104) (result : CalleeResult t u boundary 768 128)
    (dst : t.regValue .rdi = s.regValue .rdi) :
    memLoad u.external cursor 64 = memLoad t.external cursor 64 := by
  apply cursor_read_of_frame pre
  intro a ha
  apply output_copy_frame pre state result dst a
  intro region hr hin
  have hr' : region = registerRegion s .rdi 768 ∨ region = workRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ha _ (by simp) hin
  · apply ha (Stack.region s 2120) (by simp)
    have bounds := stack_bounds pre.stack
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 2120 + 2088 at hin
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧ a.toNat < (Stack.region s 2120).start + (Stack.region s 2120).size
    rw [stack_region_end]
    constructor <;> omega

end P256.Proofs.Verifying.Combination.Table
