import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Call
import P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program

theorem iterator_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {ib : Nat} (pre : Pre s boundary) (state : FrameState s t 144)
    (rip : t.RIP = entry) (dst : t.regValue .rdi = stackPtr s - 88)
    (inputBounded : (registerRegion t .rsi ib).Bounded)
    (inputAllocated : (registerRegion t .rsi ib).Allocated t.external)
    (inputApart : (registerRegion t .rsi ib).Disjoint (Stack.region s 168))
    (ret : InProgram (returnBoundary t).rip) : CalleePre t boundary entry ib 40 24 := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat-144 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hout : (t.regValue .rdi).toNat = (stackPtr s).toNat-88 := by
    rw [dst]
    exact stack_sub_toNat pre.stack (by decide)
  have stackSub : ∀ a, (Stack.region t 24).Contains a → (Stack.region s 168).Contains a := by
    intro a ha
    change (stackPtr t).toNat-24 ≤ a ∧ a < (Stack.region t 24).start+(Stack.region t 24).size at ha
    change (stackPtr s).toNat-168 ≤ a ∧ a < (Stack.region s 168).start+(Stack.region s 168).size
    rw [stack_region_end, hsp] at ha
    rw [stack_region_end]
    constructor <;> omega
  have outputSub : ∀ a, (registerRegion t .rdi 40).Contains a → (Stack.region s 168).Contains a := by
    intro a ha
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+40 at ha
    rw [hout] at ha
    change (stackPtr s).toNat-168 ≤ a ∧ a < (Stack.region s 168).start+(Stack.region s 168).size
    rw [stack_region_end]
    constructor <;> omega
  have allocated (r : MemoryRegion) (sub : ∀ a, r.Contains a → (Stack.region s 168).Contains a) :
      r.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (sub a.toNat ha))))
  refine ⟨state.bindingsSupported, state.machine, state.directionFlag, state.loaded, rip,
    inputBounded, inputAllocated, ?_, allocated _ outputSub, ?_, ?_, ?_, pre.outerBoundary, ret⟩
  · change (t.regValue .rdi).toNat+40 < 2^32
    rw [hout]
    omega
  · refine ⟨?_, allocated _ stackSub, ?_, ?_⟩
    · change (Stack.region t 24).start+(Stack.region t 24).size < 2^32
      rw [stack_region_end, hsp]
      omega
    · change 24 ≤ (stackPtr t).toNat
      rw [hsp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [hsp]
      have align : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val=0 ∧ j.val=1) ∨ (i.val=0 ∧ j.val=2) ∨ (i.val=1 ∧ j.val=2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    · have ei : i = (0 : Fin 3) := Fin.ext hi
      have ej : j = (1 : Fin 3) := Fin.ext hj
      subst i; subst j
      change (registerRegion t .rsi ib).Disjoint (registerRegion t .rdi 40)
      intro a hin hout
      exact inputApart a hin (outputSub a hout)
    · have ei : i = (0 : Fin 3) := Fin.ext hi
      have ej : j = (2 : Fin 3) := Fin.ext hj
      subst i; subst j
      change (registerRegion t .rsi ib).Disjoint (Stack.region t 24)
      intro a hin hstack
      exact inputApart a hin (stackSub a hstack)
    · have ei : i = (1 : Fin 3) := Fin.ext hi
      have ej : j = (2 : Fin 3) := Fin.ext hj
      subst i; subst j
      intro a hin hstack
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+40 at hin
      change (stackPtr t).toNat-24 ≤ a ∧ a < (Stack.region t 24).start+(Stack.region t 24).size at hstack
      rw [hout] at hin
      rw [stack_region_end, hsp] at hstack
      omega
  · intro region hr a ha forbidden
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat ha) forbidden
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha) forbidden

theorem source_preserved [Bindings] {s t : RamState} {boundary : ReturnBoundary} {n : Nat}
    {offset : BitVec 64} (pre : Pre s boundary) (state : FrameState s t offset)
    (input : Nat256At s (s.regValue .rdx) n) : Nat256At t (s.regValue .rdx) n := by
  refine ⟨input.1, ?_⟩
  intro i hi
  rw [state.frame _]
  · exact input.2 i hi
  · intro region hr hin
    have hr' : region = registerRegion s .rdi 257 ∨ region = Stack.region s 168 := by simpa using hr
    have src : (registerRegion s .rdx 32).Contains (s.regValue .rdx+BitVec.ofNat 64 i).toNat :=
      memoryRegion_contains_add pre.sourceBounded (Nat.le_refl _) (Nat.le_refl _) hi
    rcases hr' with rfl | rfl
    · exact pre.sourceOutput _ src hin
    · exact pre.sourceStack _ src hin

theorem iterator_result_work [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s entry 144)
    (result : CalleeResult entry t boundary 40 24)
    (output : entry.regValue .rdi = stackPtr s - 88) :
    MemoryWriteFrame entry t #v[workRegion s] := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr entry).toNat = (stackPtr s).toNat-144 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hout : (entry.regValue .rdi).toNat = (stackPtr s).toNat-88 := by
    rw [output]
    exact stack_sub_toNat pre.stack (by decide)
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (workRegion s) (by simp)
  have hr' : region = registerRegion entry .rdi 40 ∨ region = Stack.region entry 24 := by simpa using hr
  change (stackPtr s).toNat-168 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat-168+120
  rcases hr' with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (entry.regValue .rdi).toNat+40 at hin
    rw [hout] at hin
    constructor <;> omega
  · change (stackPtr entry).toNat-24 ≤ a.toNat ∧ a.toNat < (Stack.region entry 24).start+(Stack.region entry 24).size at hin
    rw [stack_region_end, hsp] at hin
    constructor <;> omega

theorem FrameState.after_iterator [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s entry 144)
    (result : CalleeResult entry t boundary 40 24)
    (output : entry.regValue .rdi = stackPtr s - 88) : FrameState s t := by
  have narrow := iterator_result_work pre state result output
  have work : MemoryWriteFrame entry t #v[registerRegion s .rdi 257, workRegion s] := by
    intro a ha
    exact narrow a (fun r hr => ha r (by simpa using Or.inr hr))
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre.toCalleePre work), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hsp : stackPtr t = stackPtr entry+8#64 := result.rsp
    rw [hsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre.toCalleePre work hb (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre.toCalleePre work (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem iterator_result_stack [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s entry 144)
    (result : CalleeResult entry t boundary 40 24)
    (output : entry.regValue .rdi = stackPtr s - 88) :
    MemoryWriteFrame entry t #v[Stack.region s 168] := by
  have work := iterator_result_work pre state result output
  intro a ha
  apply work a
  intro region hr hin
  have eq : region = workRegion s := by simpa using hr
  subst region
  apply ha (Stack.region s 168) (by simp)
  have bounds := stack_bounds pre.stack
  change (stackPtr s).toNat-168 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat-168+120 at hin
  change (stackPtr s).toNat-168 ≤ a.toNat ∧ a.toNat < (Stack.region s 168).start+(Stack.region s 168).size
  rw [stack_region_end]
  constructor <;> omega

theorem iterator_result_read [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s entry 144)
    (result : CalleeResult entry t boundary 40 24)
    (output : entry.regValue .rdi = stackPtr s - 88) {offset n : Nat}
    (ho : offset ≤ 136) (hl : n/8 ≤ offset+8)
    (apart : offset+40 ≤ 88 ∨ 88+n/8 ≤ offset) :
    memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) n =
      memLoad entry.external (stackPtr s - BitVec.ofNat 64 offset) n := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr entry).toNat = (stackPtr s).toNat-144 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hout : (entry.regValue .rdi).toNat = (stackPtr s).toNat-88 := by
    rw [output]
    exact stack_sub_toNat pre.stack (by decide)
  apply memLoad_congr
  intro i hi
  have addr : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat-offset+i := by
    rw [toNat_add_ofNat _ _ (by rw [stack_sub_toNat pre.stack (by omega)]; omega),
      stack_sub_toNat pre.stack (by omega)]
  change (t.external[stackPtr s - BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0 =
    (entry.external[stackPtr s - BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0
  rw [result.frame _]
  intro region hr hin
  have eq : region = registerRegion entry .rdi 40 ∨ region = Stack.region entry 24 := by simpa using hr
  rcases eq with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧
      (stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat < (entry.regValue .rdi).toNat+40 at hin
    rw [hout, addr] at hin
    omega
  · change (stackPtr entry).toNat-24 ≤ _ ∧
      (stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat < (Stack.region entry 24).start+(Stack.region entry 24).size at hin
    rw [stack_region_end, hsp, addr] at hin
    omega

end P256.Proofs.Verifying.Combination.Naf.Machine
