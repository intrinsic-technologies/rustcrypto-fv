import P256.Proofs.Field.Inverse.Setup.Initialize
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

abbrev callComponents (s : RamState) : List Component :=
  setupComponents s ++ [.reg 4, .mem (stackPtr s - 176) 8, .rip]

theorem safeGcd_parameter_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr s - 176)
    (output : t.regValue .rdi = stackPtr s - 168)
    {r : Syntax.Reg} {offset : Nat} (bounds : 32 ≤ offset ∧ offset ≤ 128)
    (address : t.regValue r = stackPtr s - BitVec.ofNat 64 offset) :
    ParameterPre t r 40 704 := by
  have stackBounds := stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 176 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (t.regValue .rdi).toNat = (stackPtr s).toNat - 168 := by
    rw [output]
    exact stack_sub_toNat pre.stack (by decide)
  have src : (t.regValue r).toNat = (stackPtr s).toNat - offset := by
    rw [address]
    exact stack_sub_toNat pre.stack (by omega)
  have endStack : (Stack.region t 704).start + (Stack.region t 704).size =
      (stackPtr s).toNat - 168 := by
    rw [stack_region_end, sp]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (t.regValue r).toNat + 32 < 2^32
    rw [src]
    omega
  · intro a ha
    change (t.regValue r).toNat ≤ a.toNat ∧ a.toNat < (t.regValue r).toNat + 32 at ha
    rw [src] at ha
    apply Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr (pre.stack.2.1 a ?_)))
    change (stackPtr s).toNat - 880 ≤ a.toNat ∧
      a.toNat < (Stack.region s 880).start + (Stack.region s 880).size
    rw [stack_region_end]
    constructor <;> omega
  · intro a ha hb
    change (t.regValue r).toNat ≤ a ∧ a < (t.regValue r).toNat + 32 at ha
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 40 at hb
    rw [src] at ha
    rw [dst] at hb
    omega
  · intro a ha hb
    change (t.regValue r).toNat ≤ a ∧ a < (t.regValue r).toNat + 32 at ha
    change (Stack.region t 704).start ≤ a ∧
      a < (Stack.region t 704).start + (Stack.region t 704).size at hb
    rw [src] at ha
    rw [endStack] at hb
    omega

theorem safeGcd_call_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (rsp : stackPtr t = stackPtr s - 168)
    (effect : (callEffect (fun _ => 0x111b70) 0x11411e t).Holds t u)
    {offset value : Nat} (low : 32 ≤ offset) (high : offset ≤ 168)
    (stored : Nat256At t (stackPtr s - BitVec.ofNat 64 offset) value) :
    Nat256At u (stackPtr s - BitVec.ofNat 64 offset) value := by
  refine ⟨stored.1, fun i hi => ?_⟩
  apply Eq.trans (effect.agrees.byte ?_) (stored.2 i hi)
  intro c hc ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  have addr : pushAddr t = stackPtr s - 176 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  rw [addr] at he
  exact stack_sub_apart pre.stack (a := 176) (b := offset) (by decide) (by omega)
    (by decide) (by omega) (.inl (by omega)) j hj i hi he.symm

theorem safeGcd_call_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (callComponents s) s t) :
    MemoryWriteFrame s t #v[Stack.region s 880] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · exact setup_writes pre c hc a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨_, by simp, ScalarFrame.stack_contains pre (offset := 176) (by decide) (by decide) ha⟩


theorem saved_words_call [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (rsp : stackPtr t = stackPtr s - 168)
    (saved : SavedWords s t)
    (effect : (callEffect (fun _ => 0x111b70) 0x11411e t).Holds t u) :
    SavedWords s u := by
  apply saved.after_frame pre
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  have push : pushAddr t = stackPtr s - 176 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  rw [push] at ha
  exact ⟨ScalarFrame.Work.region s 880 16, by simp,
    ScalarFrame.Work.contains pre (offset := 176) (by decide) (by decide) ha⟩

end P256.Proofs.Field.Inverse
