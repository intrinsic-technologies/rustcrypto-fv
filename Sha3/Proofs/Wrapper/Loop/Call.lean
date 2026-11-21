import Sha3.Proofs.Wrapper.Loop.Memory
import Sha3.Proofs.Wrapper.Loop.Code
import Sha3.Proofs.Wrapper.Finish.Call
import Sha3.Proofs.Update.Frame

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

theorem update_call_target (kind : Kind) (v : Variant) :
    branchTarget (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.callOffset v fullState)) 5 ((kind.callDisp v (keccak := keccak) (fullState := fullState)).signExtend 64) = v.updateAddress := by
  change kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.callOffset v fullState) + (5 : BitVec 64) +
    (kind.callDisp v (keccak := keccak) (fullState := fullState)).signExtend 64 = _
  rw [BitVec.add_assoc (kind.start v (keccak := keccak) (fullState := fullState)), show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl,
    ← BitVec.ofNat_add]
  exact kind.callTarget v keccak fullState

theorem call_slot_eq (initial : RamState) (v : Variant) (kind : Kind) :
    frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - (8 : BitVec 64) = stackBase (keccak := keccak) (fullState := fullState) initial v kind + (328 : BitVec 64) := by
  simp only [stackBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem stateAt_after_call {initial s called : RamState} {v : Variant} {kind : Kind}
    {state : Incremental.State}
    (h : Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) state s)
    (ha : AgreesExcept [.reg 4, .mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - (8 : BitVec 64)) 8, .rip] s called) :
    Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) state called := by
  apply h.of_bytes_eq
  intro j hj
  apply ha.byte
  intro c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover.elim
  · obtain ⟨k, hk, he⟩ := hcover
    apply state_stack_apart initial v kind j hj (328 + k) (by omega)
    rw [call_slot_eq, BitVec.add_assoc] at he
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using he
  · exact hcover.elim

theorem enter_update [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {start stop i split : Nat}
    (h : State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (hi : i < inputs.size) (hip : s.RIP = kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.callOffset v fullState))
    (hp : s.regValue .rsi = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode)
    (hinput : s.regValue .rdx = inputs[i].address)
    (hlength : s.regValue .rcx = BitVec.ofNat 64 inputs[i].bytes.size)
    (hcursor : s.regValue .rdi = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode + 200) :
    ∃ called, Advances (returnBoundary initial) 1 s called ∧
      Invariant (keccak := keccak) (fullState := fullState) initial v kind.mode called ∧
      UpdateEntryRegisters (keccak := keccak) (fullState := fullState) initial v kind inputs[i] called ∧
      stackTop called = kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.returnOffset v fullState) ∧
      Update.CallContext v called inputs[i].bytes (absorbed v inputs start i) ∧
      AgreesExcept [.reg 4, .mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - (8 : BitVec 64)) 8, .rip] s called := by
  obtain ⟨called, hrun, hinv, hrip, hsp, htop, ha, _⟩ :=
    Finish.directCallAt (kind.mode.frameSize v keccak fullState) (kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.callOffset v fullState)) (kind.callDisp v (keccak := keccak) (fullState := fullState))
      hCall (by rw [Mode.stackBudget kind.mode v keccak fullState]; omega) (by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide)
      h.invariant hip h.registers.stack (call_code kind v keccak fullState (fun hf ↦ (hCall.fullState_valid hf).1))
      (by rw [update_call_target]; cases v <;> decide)
  have hsp' : called.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - (8 : BitVec 64) := by
    change stackPtr called = _
    simp only [frameBase, BitVec.sub_sub, BitVec.ofNat_add] at hsp ⊢
    exact hsp
  have ha' : AgreesExcept [.reg 4, .mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - (8 : BitVec 64)) 8, .rip] s called := by
    simpa only [frameBase, BitVec.sub_sub, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using ha
  have hregs : UpdateEntryRegisters (keccak := keccak) (fullState := fullState) initial v kind inputs[i] called :=
    ⟨hsp', (ha'.read (n := 64) (r := 6) (by simp)).trans hp,
      (ha'.read (n := 64) (r := 2) (by simp)).trans hinput,
      (ha'.read (n := 64) (r := 1) (by simp)).trans hlength,
      (ha'.read (n := 64) (r := 7) (by simp)).trans hcursor⟩
  have htop' : stackTop called = kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.returnOffset v fullState) := by
    exact htop.trans (by simp only [Kind.returnOffset, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc])
  refine ⟨called, hrun, hinv, hregs, htop', ?_, ha'⟩
  have hinputSlice := (hCall.inputSlices kind.mode_ne_digest).inputsInMemory ⟨i, hi⟩
  have hinputValid : ValidInput initial inputs[i].region inputs[i].bytes :=
    ⟨(fun hz ↦ hinputSlice.1 (BitVec.eq_of_toNat_eq hz)), hinputSlice.2.2.2⟩
  have hread : inputs[i].region ∈ invocationReadRegions initial inputs kind.mode := by
    have hr : inputs[i].region ∈ readRegions initial inputs := by
      simp only [readRegions, List.mem_cons, Array.mem_toList_iff]
      exact Or.inr (Or.inr (Array.mem_map.mpr ⟨inputs[i], Array.getElem_mem _, rfl⟩))
    cases kind <;> exact hr
  apply update_callContext inputs[i] hCall hinv hinputValid hread hregs
    (hrip.trans (update_call_target kind v)) (stateAt_after_call h.state ha')
    (absorbed_cursor_lt v inputs start i)
  rw [htop']
  exact inProgram kind v (keccak := keccak) (fullState := fullState) (hfull := fun hf ↦ (hCall.fullState_valid hf).1) (kind.returnOffset v fullState) (by simp)

end Sha3.Proofs.Wrapper.Loop
