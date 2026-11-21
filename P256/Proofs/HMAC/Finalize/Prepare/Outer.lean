import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Prepare.Interface
import P256.Proofs.HMAC.Finalize.Prepare.Setup
import P256.Proofs.HMAC.Finalize.Prepare.Compression
import P256.Proofs.HMAC.Finalize.Call
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem outer_pad_result_byte [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : OuterPadCall initial s key)
    (result : SHA256.CompressionResult s t boundary P256.Proofs.SHA256.initialHash (keyPad key 0x5c))
    {offset len : Nat} (ho : offset ≤ 328) (hl : len ≤ offset)
    (apart : offset ≤ 56 ∨ 88 + len ≤ offset) {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack (offset := offset) (by omega)
  have addr : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [toNat_add_ofNat _ _ (by rw [low]; omega), low]
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hp : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 88 := by
    rw [state.hashPointer]
    exact stack_sub_toNat pre.stack (by decide)
  apply result.frame
  intro region member inside
  have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 336 := by
    simpa using member
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + 32 at inside
    rw [hp, addr] at inside
    omega
  · change (Stack.region s 336).start ≤ _ ∧
      _ < (Stack.region s 336).start + (Stack.region s 336).size at inside
    rw [stack_region_end, sp, addr] at inside
    omega

theorem outer_compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Initialized initial s key input) :
    ∃ fuel t, Advances boundary fuel s t ∧ OuterReady initial t key input := by
  obtain ⟨u, callRun, _, effect, frame⟩ :=
    compression_call pre state.toFrameState outerPadSite state.rip
  have memoryCall : MemoryWriteFrame s u #v[workRegion initial 672] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a covered
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    rw [call_address state.toFrameState] at covered
    exact ⟨_, by simp, work_contains pre (by decide) (by decide) covered⟩
  have stateU := state_of_work_frame pre state.state memoryCall
  have src : u.regValue .rsi = initial.regValue .rdi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.inputPointer
  have dst : u.regValue .rdi = stackPtr initial - 88 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.hashPointer
  have callState : OuterPadCall initial u key := {
    toFrameState := frame
    rip := effect.rip
    inputPointer := src
    hashPointer := dst
    countRegister := (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.countRegister
    inputBytes := by change (MemoryRegion.mk (u.regValue .rsi).toNat 64).HasBytes _ _; rw [src]; exact stateU.outer
    hashWords := by
      rw [dst]
      exact state.hash.copy (fun i hi => call_stack_byte state.toFrameState effect (by decide) (by decide) hi)
    returnInProgram := by
      change InProgram (stackTop u)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0xf9b (by decide)
  }
  obtain ⟨t, result⟩ := SHA256.compression_correct (outer_pad_pre pre callState)
  obtain ⟨fuel, run⟩ := result.execution
  have memory := outer_pad_result_frame pre callState result
  have finalFrame : ScalarFrame.FrameState initial t 0 672 328 :=
    after_result pre (by decide) frame result.toCalleeResult (work_memory_frame memory)
      (result.rsp.trans ((callEffect_stack effect).2.trans state.rsp))
  refine ⟨1 + fuel, t, callRun.trans run, finalFrame,
    result.rip.trans (callEffect_stack effect).1,
    (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans state.outputPointer),
    (result.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans state.sourcePointer),
    state_of_work_frame pre stateU memory, ?_⟩
  have position : t.external[stackPtr initial - 89#64]? = some 0 := by
    have copyResult := outer_pad_result_byte pre callState result
      (offset := 89) (len := 1) (by decide) (by decide) (Or.inr (by decide)) (i := 0) (by decide)
    have copyCall := call_stack_byte state.toFrameState effect
      (offset := 89) (len := 1) (by decide) (by decide) (i := 0) (by decide)
    simp only [BitVec.add_zero] at copyResult copyCall
    exact copyResult.trans (copyCall.trans state.position)
  have count : loadBytes t.external (stackPtr initial - 56#64) 8 = .ok 1 := by
    apply loadBytes_ok_copy (a := stackPtr initial - 56#64) (source := u.external)
      (fun i hi => outer_pad_result_byte pre callState result (by decide) (by decide) (Or.inl (by decide)) hi)
    exact loadBytes_ok_copy
      (fun i hi => call_stack_byte state.toFrameState effect (by decide) (by decide) hi) state.count
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · exact SHA256.remainderBytes_size _
    · intro i
      exact False.elim (Nat.not_lt_zero _ (by
        simpa only [SHA256.remainderBytes_size, keyPad_size, Nat.reduceMod] using i.isLt))
  · simpa only [keyPad_size, Nat.reduceMod, show UInt8.ofNat 0 = (0 : UInt8) from rfl,
      show stackPtr initial - 152#64 + 63 = stackPtr initial - 89#64 by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]] using position
  · simpa only [dst,
      show stackPtr initial - 152#64 + 64#64 = stackPtr initial - 88#64 by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd], BitVec.ofNat_eq_ofNat] using result.hashWords
  · simpa only [keyPad_size, Nat.reduceDiv,
      show stackPtr initial - 152#64 + 96#64 = stackPtr initial - 56#64 by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd], BitVec.ofNat_eq_ofNat] using count

end P256.Proofs.HMAC.Finalize.Prepare
