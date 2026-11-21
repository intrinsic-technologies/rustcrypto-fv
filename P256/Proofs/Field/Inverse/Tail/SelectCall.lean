import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Program.LimbSelect
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program.ScalarFrame (loaded_of_frame)
open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure SelectCallState [Bindings] (s t : RamState) (source : Nat) (select : Bool := true) : Prop extends FrameState s t where
  rsi : t.regValue .rsi = 4
  rcx : t.regValue .rcx = 4
  rdi : t.regValue .rdi = stackPtr s - 168
  rdx : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 source
  r8 : t.regValue .r8 = if select then 1 else 0
  rbp : t.regValue .rbp = if select then 1 else 0

theorem select_call_address [Bindings] {s t : RamState} {source : Nat} {select : Bool}
    (state : SelectCallState s t source select) : pushAddr t = stackPtr s - 176 := by
  simp only [pushAddr, state.rsp, BitVec.sub_sub, BitVec.reduceAdd]
  rfl

theorem select_call_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {source : Nat} {select : Bool} {ret : BitVec 64}
    (pre : Pre s boundary) (state : SelectCallState s t source select)
    (effect : (callEffect (fun _ => 0x1191c0) ret t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40, workRegion s] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a hcover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    rw [select_call_address state]
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ⟨i, hi, rfl⟩⟩
  · exact hcover.elim

theorem select_call_pre [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {source : Nat} {select : Bool} {ret : BitVec 64}
    (pre : Pre s boundary) (state : SelectCallState s t source select)
    (hsource : 48 ≤ source ∧ source ≤ 136) (hret : InProgram ret)
    (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x1191c0) ret t).Holds t u) :
    Program.LimbSelect.Pre u boundary := by
  have hsp : stackPtr u = stackPtr s - 176 := effect.writes.1.trans (select_call_address state)
  have hrdi : u.regValue .rdi = (stackPtr s - 168) :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have hrsi : u.regValue .rsi = 4 :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans state.rsi
  have hrdx : u.regValue .rdx = stackPtr s - BitVec.ofNat 64 source :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx
  have hrcx : u.regValue .rcx = 4 :=
    (effect.agrees.read (r := 1) (n := 64) (by simp)).trans state.rcx
  have hsrc : (stackPtr s-BitVec.ofNat 64 source).toNat = (stackPtr s).toNat-source :=
    P256.Proofs.Program.stack_sub_toNat pre.stack (by omega)
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hspn : (stackPtr u).toNat = (stackPtr s).toNat - 176 := by
    rw [hsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have hscratch : ((stackPtr s - 168)).toNat = (stackPtr s).toNat - 168 :=
    P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have hout : (registerRegion u .rdi 32).start = (stackPtr s).toNat - 168 := by
    change (u.regValue .rdi).toNat = _
    rw [hrdi, hscratch]
  have hstack : (Stack.region u 80).start = (stackPtr s).toNat - 256 := by
    change (stackPtr u).toNat - 80 = _
    rw [hspn]
    omega
  have hend : (Stack.region u 80).start + (Stack.region u 80).size = (stackPtr s).toNat - 168 := by
    rw [P256.Proofs.Program.stack_region_end]
    change (stackPtr u).toNat + 8 = _
    rw [hspn]
    omega
  have stackSub : ∀ a, (Stack.region u 80).Contains a → (Stack.region s 880).Contains a := by
    intro a ha
    change (Stack.region u 80).start ≤ a ∧ a < (Stack.region u 80).start + (Stack.region u 80).size at ha
    rw [hend, hstack] at ha
    change (stackPtr s).toNat - 880 ≤ a ∧ a < (Stack.region s 880).start + (Stack.region s 880).size
    rw [P256.Proofs.Program.stack_region_end]
    change (stackPtr s).toNat - 880 ≤ a ∧ a < (stackPtr s).toNat+8
    constructor <;> omega
  have outputSub : ∀ a, (registerRegion u .rdi 32).Contains a → (Stack.region s 880).Contains a := by
    intro a ha
    change (registerRegion u .rdi 32).start ≤ a ∧ a < (registerRegion u .rdi 32).start + 32 at ha
    rw [hout] at ha
    change (stackPtr s).toNat - 880 ≤ a ∧ a < (Stack.region s 880).start + (Stack.region s 880).size
    rw [P256.Proofs.Program.stack_region_end]
    change (stackPtr s).toNat - 880 ≤ a ∧ a < (stackPtr s).toNat + 8
    constructor <;> omega
  have allocated : ∀ a, (s.external[a]?).isSome → (u.external[a]?).isSome :=
    fun a h => effect.agrees.grow a (state.allocated a h)
  have frame := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre (select_call_frame pre state effect))
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
  · exact ScalarFrame.loaded_of_frame pre frame
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
    · exact pre.avoids (Stack.region s 880) (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids (Stack.region s 880) (by simp) a (stackSub a.toNat ha)
  · have ret := (callEffect_stack effect).1
    change InProgram (stackTop u)
    rw [ret]
    exact hret
  · change (u.regValue .rdx).toNat + 32 < 2^32
    rw [hrdx, hsrc]
    omega
  · intro a ha
    change (u.regValue .rdx).toNat ≤ a.toNat ∧ a.toNat < (u.regValue .rdx).toNat+32 at ha
    rw [hrdx, hsrc] at ha
    apply Option.isSome_iff_exists.mp (allocated a (Option.isSome_iff_exists.mpr (pre.stack.2.1 a ?_)))
    change (stackPtr s).toNat-880 ≤ a.toNat ∧ a.toNat < (Stack.region s 880).start+(Stack.region s 880).size
    rw [P256.Proofs.Program.stack_region_end]
    constructor <;> omega
  · intro a ha ho
    change (u.regValue .rdx).toNat ≤ a ∧ a < (u.regValue .rdx).toNat+32 at ha
    change (registerRegion u .rdi 32).start ≤ a ∧ a < (registerRegion u .rdi 32).start+32 at ho
    rw [hrdx, hsrc] at ha
    rw [hout] at ho
    omega
  · intro a ha hs
    change (u.regValue .rdx).toNat ≤ a ∧ a < (u.regValue .rdx).toNat+32 at ha
    change (Stack.region u 80).start ≤ a ∧ a < (Stack.region u 80).start+(Stack.region u 80).size at hs
    rw [hrdx, hsrc] at ha
    rw [hend] at hs
    omega

end P256.Proofs.Field.Inverse
