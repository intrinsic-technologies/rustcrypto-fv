import P256.Proofs.Verifying.Message.Hash.Finalize.Interface
import P256.Proofs.Verifying.Message.Hash.Finalize.Copy.Setup
import P256.Proofs.HMAC.State
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Buffered initial s boundary message) :
    ∃ t, Copied initial t boundary message := by
  obtain ⟨fuelA, a, runA, readyA, _, effectA⟩ := Copy.setup_run boundary
    pre.outerBoundary s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd71d Copy.setupBytes
      (by decide) (by decide +kernel)) state.rip
  have agreesA : AgreesExcept [.reg 7, .reg 6, .reg 1, .rip] s a := effectA.agrees
  have frameA := state.toFrameState.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp)
  have memoryA : a.external = s.external := agreesA.external (by simp [Component.Covers])
  have destA : a.regValue .rdi = stackPtr a + 128 := by
    exact effectA.writes.1.trans (congrArg (· + 128) (frameA.rsp.trans state.rsp.symm)).symm
  have sourceA : a.regValue .rsi = stackPtr a + 472 := by
    exact effectA.writes.2.1.trans (congrArg (· + 472)
      (frameA.rsp.trans state.rsp.symm)).symm
  have countA : a.regValue .rcx = 13 := effectA.writes.2.2
  have hn : (rcx.read a).toNat = 13 := by change (a.regValue .rcx).toNat = 13; rw [countA]; rfl
  have src : MemReadable a (rsi.read a) (8 * 13) := by
    change MemReadable a (a.regValue .rsi) 104
    rw [sourceA]
    exact ScalarFrame.stack_readable pre.toCalleePre frameA (by decide) (by decide)
  have dst : Instructions.CrossPageStore.Writable a (rdi.read a) (8 * 13) := by
    change Instructions.CrossPageStore.Writable a (a.regValue .rdi) 104
    rw [destA]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      ScalarFrame.stack_writable pre.toCalleePre frameA (offset := 128) (len := 104)
        (by decide) (by decide) (by decide)
  have apart : (rsi.read a).toNat + 8 * 13 ≤ (rdi.read a).toNat ∨
      (rdi.read a).toNat + 8 * 13 ≤ (rsi.read a).toNat := by
    right
    change (a.regValue .rdi).toNat + 104 ≤ (a.regValue .rsi).toNat
    rw [destA, sourceA]
    change (stackPtr a + BitVec.ofNat 64 128).toNat + 104 ≤ (stackPtr a + BitVec.ofNat 64 472).toNat
    rw [ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide : 472 ≤ 1176),
      ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide : 128 ≤ 1176)]
    change (stackPtr initial - BitVec.ofNat 64 1048).toNat + 104 ≤
      (stackPtr initial - BitVec.ofNat 64 704).toNat
    rw [stack_sub_toNat pre.stack (by decide), stack_sub_toNat pre.stack (by decide)]
    have bounds := stack_bounds pre.stack
    omega
  have pc := Instructions.RepMovsqAny.pre_of_memory effectA.rip
    frameA.directionFlag.df hn src dst apart
    (by change RangeApart (a.regValue .rdi) 104
          (Extracted.textAddress + BitVec.ofNat 64 0xd732) 3
        rw [destA]
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          ScalarFrame.stack_code pre.toCalleePre frameA (offset := 128) (len := 104)
            (codeOffset := 0xd732) (codeLen := 3) (by decide) (by decide) (by decide))
  obtain ⟨run, ready, effect, copied⟩ := Instructions.RepMovsqAny.rep_movsq_execution
    pre.bindingsSupported.stringStride readyA
    (programText_slice (programLoaded_codeIn frameA.loaded) 0xd732 [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd732 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd735 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize ht : nextStates 13 a = t at run ready effect copied
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (stackPtr a + 128) 104, .rip] a t := by
    simpa only [repMovsqEffect_components, hn, Nat.reduceMul,
      show rdi.read a = stackPtr a + 128 from destA] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7, .reg 1, .mem (stackPtr a + 128) 104, .rip]
      #v[ScalarFrame.workRegion initial 9992] := by
    intro c hc addr covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    change (Component.mem (stackPtr a + BitVec.ofNat 64 128) 104).Covers addr at covered
    rw [ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide : 128 ≤ 1176)] at covered
    exact ⟨_, by simp, ScalarFrame.work_contains pre.toCalleePre
      (by decide) (by decide) covered⟩
  have frameT := frameA.after_effect pre.toCalleePre (by decide) ready agrees (by
    intro c hc addr covered
    obtain ⟨region, member, inside⟩ := writes c hc addr covered
    exact ⟨region, by simpa using Or.inr member, inside⟩) (by simp)
  have saved (offset : Nat) (low : 232 ≤ offset) (high : offset + 8 < 2^64) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    rw [← memoryA]
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (a.external[_]?).getD 0
    rw [agrees.byte]
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    have sp : stackPtr a = frameBase initial := frameA.rsp
    rw [sp, BitVec.add_assoc, BitVec.add_assoc] at eq
    have eqn := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase initial)).mp eq)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at eqn
    omega
  refine ⟨t, ⟨⟨frameT, ?_, ?_, ?_, ?_, ?_⟩, effect.rip, ?_⟩⟩
  · obtain ⟨fuel, execution⟩ := state.execution
    exact ⟨fuel + fuelA + 13, (execution.trans runA).trans run⟩
  · exact (saved 456 (by decide) (by decide)).trans state.savedKey
  · exact (saved 384 (by decide) (by decide)).trans state.savedOutput
  · exact (saved 464 (by decide) (by decide)).trans state.savedSignature
  · have memory := agrees.memoryWriteFrame writes
    have initialFrame : MemoryWriteFrame initial a #v[Stack.region initial 9992] := by
      intro addr outside
      rw [memoryA]
      exact state.stackFrame addr outside
    exact memoryWriteFrame_trans initialFrame (work_frame_stack pre.toCalleePre memory)
  · apply state.hash.copy
    change ∀ i < 104, t.external[a.regValue .rdi + BitVec.ofNat 64 i]? =
      a.external[a.regValue .rsi + BitVec.ofNat 64 i]? at copied
    simpa only [destA, sourceA, frameA.rsp, memoryA, frameBase] using copied

end P256.Proofs.Verifying.Message.Hash.Finalize
