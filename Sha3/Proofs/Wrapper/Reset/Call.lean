import Sha3.Proofs.Wrapper.Reset.Selection
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Wrapper.Finish.Call
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple

namespace Sha3.Proofs.Wrapper.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def preparePC (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : BitVec 64 :=
  ((if finalize then finalizeMode else Mode.reset).entry v keccak fullState).entryAddress +
    (if !finalize then 0x84 else match finalizeMode with
    | .finalizeFixedReset | .digestFinalizeReset =>
      if fullState then 0xa4 else if v = .sha384 ∨ v = .sha512 then 0xa8 else 0x99
    | _ => 0x99)

def prepareChanges : List Component := [.reg 7, .reg 2, .reg 6, .flags, .rip]

theorem prepareChanges_noMem : ∀ c ∈ prepareChanges, ∀ address, ¬ c.Covers address := by
  simp [prepareChanges, Component.Covers]

theorem prepare_state [bindings : Bindings] (v : Variant) (finalize : Bool) {keccak fullState : Bool} {finalizeMode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v (mode finalize finalizeMode) initial inputs split keccak fullState)
    (inv : Invariant initial v (mode finalize finalizeMode) s keccak fullState) (hp : s.RIP = preparePC v finalize keccak fullState finalizeMode)
    (hs : stackPtr s = frameBase initial v (mode finalize finalizeMode) keccak fullState)
    (hDirect : finalizeMode = .finalizeReset ∨ finalizeMode = .digestFinalizeIntoReset := by exact Or.inl rfl) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v (mode finalize finalizeMode) t keccak fullState ∧
      t.RIP = preparePC v finalize keccak fullState finalizeMode + (5 : BitVec 64) ∧
      (Operand.reg 7 : Operand 64).read t = statePointer initial v (mode finalize finalizeMode) keccak fullState ∧
      AgreesExcept prepareChanges s t := by
  have sp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases finalize <;> cases v <;> decide +kernel
  obtain ⟨t, ht, it, _, et, ag⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (preparePC v finalize keccak fullState finalizeMode) 0x48
      (by unfold RexWPrefix; decide +kernel) 7 (stateMode finalize finalizeMode v fullState)
      (by rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases finalize <;> cases v <;> decide +kernel) (by rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases finalize <;> cases v <;> decide +kernel)
      (by rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases finalize <;> cases v <;> decide +kernel))
    (by unfold ImageAt; rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases finalize <;> cases v <;> decide +kernel)
    (by change ∀ c ∈ [.reg 7, .rip], c ∈ prepareChanges; simp [prepareChanges])
    prepareChanges_noMem (by simp [prepareChanges]) inv sp hp
  refine ⟨t, ht, it, ?_, ?_, ag⟩
  · have hh := et.rip
    rcases hDirect with rfl | rfl <;> cases finalize <;> cases v <;> cases fullState <;> simpa [leaR64Effect, leaLen, stateMode, mode, AddrMode.tail,
      Disp.bytes, immBytes, BitVec.add_assoc] using hh
  · have hh := et.writes
    rcases hDirect with rfl | rfl <;> cases finalize
    all_goals first
      | exact hh.trans (congrArg (fun x : BitVec 64 ↦ x + 8) hs)
      | exact hh.trans (congrArg (fun x : BitVec 64 ↦ x + 24) hs)

theorem prepare_reset [bindings : Bindings] (v : Variant) {keccak fullState : Bool}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v .reset initial inputs split keccak fullState)
    (inv : Invariant initial v .reset s keccak fullState) (hp : s.RIP = preparePC v false keccak fullState)
    (hs : stackPtr s = frameBase initial v .reset keccak fullState) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧ Invariant initial v .reset t keccak fullState ∧
      t.RIP = preparePC v false keccak fullState + (12 : BitVec 64) ∧ SetupRegisters initial v .reset t keccak fullState ∧
      AgreesExcept prepareChanges s t := by
  obtain ⟨s1, h1, i1, ip1, ptr1, a1⟩ := prepare_state (finalizeMode := .finalizeReset) v false hCall inv hp hs
  have sp1 : s1.GPR[4] ≠ (returnBoundary initial).rsp := by
    have he : s1.GPR[4] = s.GPR[4] := a1.agree (.reg 4) (by simp [prepareChanges]) rfl
    rw [he]
    change stackPtr s ≠ _
    rw [hs, frameBase]
    exact Finish.stackSub_ne_returnBoundary initial _ (by cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
  obtain ⟨s2, h2, i2, sp2, e2, a2⟩ := advanceNoMemory hCall
    (mov_r32_imm32_effect_step (preparePC v false keccak fullState + (5 : BitVec 64)) 0xba (by decide +kernel) 201)
    (by unfold ImageAt; cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
    (by change ∀ c ∈ [.reg 2, .rip], c ∈ prepareChanges; simp [prepareChanges])
    prepareChanges_noMem (by simp [prepareChanges]) i1 sp1 ip1
  change (movR32Imm32Effect (preparePC v false keccak fullState + 5) 5 2 201 s1).Holds s1 s2 at e2
  have ip2 : s2.RIP = preparePC v false keccak fullState + (10 : BitVec 64) := by
    simpa only [movR32Imm32Effect, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] using e2.rip
  obtain ⟨s3, h3, i3, _, e3, a3⟩ := advanceNoMemory hCall
    (xor_r32_r32_effect_step (preparePC v false keccak fullState + (10 : BitVec 64)) 0xf6 (by decide +kernel))
    (by unfold ImageAt; cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
    (by change ∀ c ∈ [.reg 6, .flags, .rip], c ∈ prepareChanges; simp [prepareChanges])
    prepareChanges_noMem (by simp [prepareChanges]) i2 sp2 ip2
  change (xorR32R32Effect (preparePC v false keccak fullState + 10) 2 6 6 s2).Holds s2 s3 at e3
  have aa : AgreesExcept prepareChanges s s3 :=
    (a1.trans (a2.trans a3)).mono (by
      intro c hc
      simpa only [List.mem_append, or_self] using hc)
  refine ⟨s3, h1.trans (h2.trans h3), i3, ?_, ⟨?_, ?_, ?_, ?_⟩, aa⟩
  · simpa only [xorR32R32Effect, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] using e3.rip
  · exact (aa.read (n := 64) (r := 4) (by simp [prepareChanges])).trans hs
  · rw [e3.agrees.read (r := 7) (by simp [xorR32R32Effect_components]),
      e2.agrees.read (r := 7) (by simp [movR32Imm32Effect_components])]
    exact ptr1
  · rw [e3.agrees.read (r := 2) (by simp [xorR32R32Effect_components])]
    exact e2.writes
  · have hw := e3.writes
    change (Operand.reg 6 : Operand 64).read s3 = _ at hw
    change (Operand.reg 6 : Operand 64).read s3 = (0 : BitVec 64)
    apply hw.trans
    change (((Operand.reg 6 : Operand 32).read s2) ^^^
      ((Operand.reg 6 : Operand 32).read s2)).setWidth 64 = (0 : BitVec 64)
    rw [BitVec.xor_self]
    rfl

def memsetDisp (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : BitVec 32 :=
  (0x200188 - (preparePC v false keccak fullState + (18 : BitVec 64))).setWidth 32

def resetChanges (initial : RamState) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : List Component :=
  prepareChanges ++ initializationChanges initial v .reset keccak fullState

theorem reset_steps [bindings : Bindings] (hstride : UnitStringStride bindings) (v : Variant) {keccak fullState : Bool}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v .reset initial inputs split keccak fullState)
    (inv : Invariant initial v .reset s keccak fullState) (saved : SavedFrame initial s .reset fullState)
    (hp : s.RIP = preparePC v false keccak fullState) (hs : stackPtr s = frameBase initial v .reset keccak fullState) :
    ∃ t, Advances (returnBoundary initial) 49 s t ∧ Invariant initial v .reset t keccak fullState ∧
      t.RIP = comparePC v false keccak fullState ∧ Initialized initial v .reset t keccak fullState ∧
      AgreesExcept (resetChanges initial v keccak fullState) s t := by
  obtain ⟨u, hu, iu, ipu, ru, au⟩ := prepare_reset v hCall inv hp hs
  have savedu := saved.of_external_eq (au.external prepareChanges_noMem)
  obtain ⟨t, ht, it, ipt, initialized, ag, _⟩ := initial_memset_steps hstride
    (returnBoundary initial) (preparePC v false keccak fullState + (12 : BitVec 64)) (memsetDisp v keccak fullState) hCall
    (by rw [Mode.stackBudget .reset v keccak fullState]; omega)
    (by unfold ImageAt; cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
    (by cases keccak <;> cases fullState <;> cases v <;> decide +kernel) (by cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
    iu savedu ipu ru
    (by
      rw [frameBase, BitVec.sub_sub]
      exact Finish.stackSub_ne_returnBoundary initial _ (by cases keccak <;> cases fullState <;> cases v <;> decide +kernel))
    (by rw [frameBase]; exact Finish.stackSub_ne_returnBoundary initial _ (by cases keccak <;> cases fullState <;> cases v <;> decide +kernel))
  refine ⟨t, hu.trans ht, it, ?_, initialized, au.trans ag⟩
  have hpc : preparePC v false keccak fullState + (12 : BitVec 64) + 6 = comparePC v false keccak fullState := by cases keccak <;> cases fullState <;> cases v <;> decide +kernel
  exact ipt.trans hpc

end Sha3.Proofs.Wrapper.Reset
