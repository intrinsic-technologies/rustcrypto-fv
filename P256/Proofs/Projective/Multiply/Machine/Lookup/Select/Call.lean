import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Memory
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_step [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : CallState s t select) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x1191c0) 0x1143bf t).Holds t u := by
  have haddr : pushAddr t = stackPtr s - 48 := by
    simp only [pushAddr, state.rsp, scratch, BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have code : CodeIn (codeRange 0x1143ba [0xe8, 0x1, 0x4e, 0, 0]) t :=
    P256.Proofs.Program.programText_slice (P256.Proofs.Program.programLoaded_codeIn state.loaded)
      0x143ba _ (by decide) (by decide +kernel)
  have hpush : PushPre 0x1143ba 5 t := by
    refine ⟨state.rip, ?_, ?_⟩
    · rw [haddr]
      exact state.toSavedState.stack_writable8 pre (by decide) (by decide)
    · rw [haddr]
      exact stack_codeApart pre (by decide) (by decide) (text_range (offset := 0x143ba) (by decide))
  exact (call_rel32_effect_step 0x1143ba 0x4e01 (by decide)).advances
    (P256.Proofs.Program.readyToStep state.machine state.bindingsSupported) code hpush
    (P256.Proofs.Program.boundary_ne_program pre.outerBoundary
      (P256.Proofs.Program.inProgram_of_textOffset 0x191c0 (by decide)))

theorem call_address [Bindings] {s t : RamState} {select : Bool} (state : CallState s t select) :
    pushAddr t = stackPtr s - 48 := by
  simp only [pushAddr, state.rsp, scratch, BitVec.sub_sub, BitVec.reduceAdd]
  rfl

theorem call_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : CallState s t select)
    (effect : (callEffect (fun _ => 0x1191c0) 0x1143bf t).Holds t u) :
    MemoryWriteFrame t u #v[Stack.region s 128] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a hcover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    rw [call_address state]
    exact ⟨Stack.region s 128, by simp, stack_contains pre (by decide) (by decide) hi⟩
  · exact hcover.elim

theorem call_pre [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : CallState s t select)
    (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x1191c0) 0x1143bf t).Holds t u) :
    Program.LimbSelect.Pre u boundary := by
  have hsp : stackPtr u = stackPtr s - 48 := effect.writes.1.trans (call_address state)
  have hrdi : u.regValue .rdi = scratch s :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have hrsi : u.regValue .rsi = 4 :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans state.rsi
  have hrdx : u.regValue .rdx = s.regValue .rdx :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx
  have hrcx : u.regValue .rcx = 4 :=
    (effect.agrees.read (r := 1) (n := 64) (by simp)).trans state.rcx
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hspn : (stackPtr u).toNat = (stackPtr s).toNat - 48 := by
    rw [hsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have hscratch : (scratch s).toNat = (stackPtr s).toNat - 40 :=
    P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have hout : (registerRegion u .rdi 32).start = (stackPtr s).toNat - 40 := by
    change (u.regValue .rdi).toNat = _
    rw [hrdi, hscratch]
  have hstack : (Stack.region u 80).start = (stackPtr s).toNat - 128 := by
    change (stackPtr u).toNat - 80 = _
    rw [hspn]
    omega
  have hend : (Stack.region u 80).start + (Stack.region u 80).size = (stackPtr s).toNat - 40 := by
    rw [P256.Proofs.Program.stack_region_end]
    change (stackPtr u).toNat + 8 = _
    rw [hspn]
    omega
  have stackSub : ∀ a, (Stack.region u 80).Contains a → (Stack.region s 128).Contains a := by
    intro a ha
    change (Stack.region u 80).start ≤ a ∧ a < (Stack.region u 80).start + (Stack.region u 80).size at ha
    rw [hend, hstack] at ha
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (Stack.region s 128).start + (Stack.region s 128).size
    rw [P256.Proofs.Program.stack_region_end]
    exact ⟨ha.1, by change a < (stackPtr s).toNat + 8; omega⟩
  have outputSub : ∀ a, (registerRegion u .rdi 32).Contains a → (Stack.region s 128).Contains a := by
    intro a ha
    change (registerRegion u .rdi 32).start ≤ a ∧ a < (registerRegion u .rdi 32).start + 32 at ha
    rw [hout] at ha
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (Stack.region s 128).start + (Stack.region s 128).size
    rw [P256.Proofs.Program.stack_region_end]
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (stackPtr s).toNat + 8
    constructor <;> omega
  have allocated : ∀ a, (s.external[a]?).isSome → (u.external[a]?).isSome :=
    fun a h => effect.agrees.grow a (state.allocated a h)
  have frame := memoryWriteFrame_trans state.frame (call_frame pre state effect)
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees
    machine := P256.Proofs.Program.supportedMachine_of_ready_agrees state.machine ready effect.agrees
    directionFlag := effect.agrees.directionFlagClear (by simp) state.directionFlag
    loaded := ?_
    rip := effect.rip
    inputBounded := ?_
    inputAllocated := ?_
    outputBounded := ?_
    outputAllocated := ?_
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ?_
    leftCount := hrsi
    rightCount := hrcx
    sourceBounded := ?_
    sourceAllocated := ?_
    sourceOutput := ?_
    sourceStack := ?_
  }
  · intro a b hf
    rw [frame a]
    · exact pre.loaded a b hf
    · intro region hr ha
      have : region = Stack.region s 128 := by simpa using hr
      subst region
      exact pre.avoids _ (by simp) a ha (.inl ⟨b, hf⟩)
  · change (u.regValue .rsi).toNat + 0 < 2^32
    rw [hrsi]
    decide
  · intro a ha
    have : False := by
      change (u.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (u.regValue .rsi).toNat + 0 at ha
      omega
    exact this.elim
  · change (registerRegion u .rdi 32).start + 32 < 2^32
    rw [hout]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (outputSub a.toNat ha))))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change (Stack.region u 80).start + (Stack.region u 80).size < 2^32
      rw [hend]
      omega
    · intro a ha
      exact Option.isSome_iff_exists.mp (allocated a
        (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (stackSub a.toNat ha))))
    · change 80 ≤ (stackPtr u).toNat
      rw [hspn]
      omega
    · change (stackPtr u).toNat % 16 = 8
      rw [hspn]
      have : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hindices : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) := by
      change i.val < j.val at hij
      omega
    rcases hindices with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · intro a ha
      change (u.regValue .rsi).toNat ≤ a ∧ a < (u.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha
      change (u.regValue .rsi).toNat ≤ a ∧ a < (u.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha hs
      change (registerRegion u .rdi 32).start ≤ a ∧ a < (registerRegion u .rdi 32).start + 32 at ha
      change (Stack.region u 80).start ≤ a ∧ a < (Stack.region u 80).start + (Stack.region u 80).size at hs
      rw [hout] at ha
      rw [hend] at hs
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids (Stack.region s 128) (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids (Stack.region s 128) (by simp) a (stackSub a.toNat ha)
  · have ret := (callEffect_stack effect).1
    change InProgram (stackTop u)
    rw [ret]
    exact P256.Proofs.Program.inProgram_of_textOffset 0x143bf (by decide)
  · change (u.regValue .rdx).toNat + 32 < 2^32
    rw [hrdx]
    exact pre.rightBounded
  · intro a ha
    have hc : (registerRegion s .rdx 32).Contains a.toNat := by
      simpa only [registerRegion, hrdx] using ha
    exact Option.isSome_iff_exists.mp (allocated a (Option.isSome_iff_exists.mpr (pre.rightAllocated a hc)))
  · intro a ha ho
    have hc : (registerRegion s .rdx 32).Contains a := by simpa only [registerRegion, hrdx] using ha
    exact pre.rightStack a hc (outputSub a ho)
  · intro a ha hs
    have hc : (registerRegion s .rdx 32).Contains a := by simpa only [registerRegion, hrdx] using ha
    exact pre.rightStack a hc (stackSub a hs)

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
