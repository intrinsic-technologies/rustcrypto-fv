import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Call
import P256.Proofs.Program.LimbSelect

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleeResult)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem returned_state [Bindings] {s t u v : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : CallState s t select)
    (effect : (callEffect (fun _ => 0x1191c0) 0x1143bf t).Holds t u)
    (result : CalleeResult u v boundary 32 80) (selected : Program.LimbSelect.SelectedBytesAt u v select) :
    ReturnedState s v select := by
  have hsp : stackPtr u = stackPtr s - 48 := effect.writes.1.trans (call_address state)
  have hrdi : u.regValue .rdi = scratch s :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have hrdx : u.regValue .rdx = s.regValue .rdx :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hspn : (stackPtr u).toNat = (stackPtr s).toNat - 48 := by
    rw [hsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have hscratch : (scratch s).toNat = (stackPtr s).toNat - 40 :=
    P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  let region : MemoryRegion := ⟨(stackPtr s).toNat - 128, 120⟩
  have contains : ∀ a, region.Contains a → (Stack.region s 128).Contains a := by
    intro a ha
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (stackPtr s).toNat - 128 + 120 at ha
    change (stackPtr s).toNat - 128 ≤ a ∧ a < (Stack.region s 128).start + (Stack.region s 128).size
    rw [P256.Proofs.Program.stack_region_end]
    exact ⟨ha.1, by change a < (stackPtr s).toNat + 8; omega⟩
  have rawFrame : MemoryWriteFrame u v #v[region] := by
    intro a hout
    apply result.frame a
    intro r hr hin
    apply hout region (by simp)
    have hr' : r = registerRegion u .rdi 32 ∨ r = Stack.region u 80 := by simpa using hr
    change (stackPtr s).toNat - 128 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 128 + 120
    rcases hr' with rfl | rfl
    · change (u.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (u.regValue .rdi).toNat + 32 at hin
      rw [hrdi, hscratch] at hin
      constructor <;> omega
    · change (stackPtr u).toNat - 80 ≤ a.toNat ∧
        a.toNat < (Stack.region u 80).start + (Stack.region u 80).size at hin
      rw [P256.Proofs.Program.stack_region_end] at hin
      change (stackPtr u).toNat - 80 ≤ a.toNat ∧ a.toNat < (stackPtr u).toNat + 8 at hin
      rw [hspn] at hin
      constructor <;> omega
  have pushFrame : MemoryWriteFrame t u #v[region] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a hv
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hv.elim
    · obtain ⟨i, hi, rfl⟩ := hv
      rw [call_address state]
      refine ⟨region, by simp, ?_⟩
      change (stackPtr s).toNat - 128 ≤ (stackPtr s - 48 + BitVec.ofNat 64 i).toNat ∧
        (stackPtr s - 48 + BitVec.ofNat 64 i).toNat < (stackPtr s).toNat - 128 + 120
      have hn := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 48) (by decide)
      change (stackPtr s - 48).toNat = (stackPtr s).toNat - 48 at hn
      rw [toNat_add_ofNat _ _ (by rw [hn]; omega), hn]
      constructor <;> omega
    · exact hv.elim
  have smallFrame := memoryWriteFrame_trans pushFrame rawFrame
  have stableByte (a : BitVec 64) (ha : (stackPtr s).toNat - 8 ≤ a.toNat) :
      v.external[a]? = t.external[a]? := by
    apply smallFrame a
    intro r hr hin
    have : r = region := by simpa using hr
    subst r
    change (stackPtr s).toNat - 128 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 128 + 120 at hin
    omega
  have stableWord {offset : Nat} (ho : offset ≤ 8) :
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand 64).read v =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand 64).read t := by
    apply memLoad_congr
    intro i hi
    have hn := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := offset) (by omega)
    change (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset at hn
    have ha : (stackPtr s).toNat - 8 ≤ (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
      rw [toNat_add_ofNat _ _ (by rw [hn]; omega), hn]
      omega
    simp only [memByte, PhysicalMemory.read, stableByte _ ha]
  have callStable {a : BitVec 64} (ha : ¬ Component.Covers (.mem (pushAddr t) 8) a) :
      u.external[a]? = t.external[a]? := by
    exact effect.agrees.byte (by
      intro c hc hv
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hv.elim
      · exact ha hv
      · exact hv.elim)
  refine {
    bindingsSupported := result.bindingsSupported
    machine := result.machine
    loaded := result.loaded
    allocated := fun a ha => result.allocated a (effect.agrees.grow a (state.allocated a ha))
    frame := ?_
    registers := ?_
    directionFlag := result.directionFlag
    mxcsr := result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans state.mxcsr)
    fp87 := result.fp87.trans ((effect.agrees.fcw (by simp)).trans state.fp87)
    rsp := ?_
    rbx := ?_
    savedRbx := (stableWord (offset := 8) (by decide)).trans state.savedRbx
    returnWord := ?_
    rip := ?_
    selected := ?_
  }
  · exact memoryWriteFrame_trans state.frame (fun a hout => smallFrame a (by
      intro r hr hin
      have : r = region := by simpa using hr
      subst r
      exact hout (Stack.region s 128) (by simp) (contains a.toNat hin)))
  · intro r hr
    have hp : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15] := List.mem_cons_of_mem .rbx hr
    rw [result.calleeSaved r hp]
    apply Eq.trans _ (state.registers r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (r := 5) (n := 64) (by simp)
    · exact effect.agrees.read (r := 12) (n := 64) (by simp)
    · exact effect.agrees.read (r := 13) (n := 64) (by simp)
    · exact effect.agrees.read (r := 14) (n := 64) (by simp)
    · exact effect.agrees.read (r := 15) (n := 64) (by simp)
  · change v.regValue .rsp = scratch s
    rw [result.rsp]
    exact (callEffect_stack effect).2.trans state.rsp
  · rw [result.calleeSaved .rbx (by simp)]
    exact (effect.agrees.read (r := 3) (n := 64) (by simp)).trans state.rbx
  · have hs := stableWord (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at hs
    exact hs.trans state.returnWord
  · exact result.rip.trans (callEffect_stack effect).1
  · intro i hi
    have hselected := selected i hi
    rw [hrdi, hrdx] at hselected
    rw [hselected]
    unfold outputBytes
    split
    · rw [callStable]
      · exact state.source i hi
      · intro hv
        obtain ⟨j, hj, heq⟩ := hv
        rw [call_address state] at heq
        apply pre.rightStack _
          (P256.Proofs.Program.memoryRegion_contains_add pre.rightBounded (Nat.le_refl _) (Nat.le_refl _) hi)
        exact heq ▸ stack_contains pre (offset := 48) (len := 8) (by decide) (by decide) hj
    · rw [callStable]
      · exact state.copied i hi
      · intro hv
        obtain ⟨j, hj, heq⟩ := hv
        rw [call_address state] at heq
        have hn := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 48) (by decide)
        change (stackPtr s - 48).toNat = (stackPtr s).toNat - 48 at hn
        have he := congrArg BitVec.toNat heq
        rw [toNat_add_ofNat _ _ (by rw [hscratch]; omega), hscratch,
          toNat_add_ofNat _ _ (by rw [hn]; omega), hn] at he
        omega

theorem call_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : CallState s t select) :
    ∃ fuel v, Advances boundary fuel t v ∧ ReturnedState s v select := by
  obtain ⟨u, run, ready, effect⟩ := call_step pre state
  have choice : (u.regValue .r8).setWidth 8 = if select then 1 else 0 :=
    (congrArg (BitVec.setWidth 8) (effect.agrees.read (r := 8) (n := 64) (by simp))).trans state.r8
  obtain ⟨v, result, selected⟩ := Program.LimbSelect.limb_select32_low8_correct (call_pre pre state ready effect) choice
  obtain ⟨fuel, run'⟩ := result.execution
  exact ⟨1 + fuel, v, run.trans run', returned_state pre state effect result selected⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
