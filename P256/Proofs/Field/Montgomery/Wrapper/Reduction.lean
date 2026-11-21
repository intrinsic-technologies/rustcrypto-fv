import P256.Proofs.Field.Montgomery.Wrapper.ReductionPre
import P256.Proofs.Field.Montgomery.Wrapper.Call
import P256.Proofs.Field.Montgomery.Wrapper.Bytes
import P256.Proofs.Field.Montgomery.Reduction

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem reduction_work_frame (pre : CalleePre s boundary entryPC 32 32 280)
    (rsp : stackPtr t = stackPtr s - 144)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (result : CalleeResult t u boundary 32 56) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 32, workRegion s] := by
  have hb := stack_bounds pre.stack
  have hspn : (stackPtr t).toNat = (stackPtr s).toNat - 144 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  intro a hout
  apply result.frame a
  intro r hr hin
  have hr' : r = registerRegion t .rdi 32 ∨ r = Stack.region t 56 := by simpa using hr
  rcases hr' with rfl | rfl
  · apply hout (registerRegion s .rdi 32) (by simp)
    simpa only [registerRegion, destination] using hin
  · apply hout (workRegion s) (by simp)
    change (stackPtr s).toNat - 280 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 280 + 272
    change (stackPtr t).toNat - 56 ≤ a.toNat ∧
      a.toNat < (Stack.region t 56).start + (Stack.region t 56).size at hin
    rw [stack_region_end] at hin
    change (stackPtr t).toNat - 56 ≤ a.toNat ∧ a.toNat < (stackPtr t).toNat + 8 at hin
    rw [hspn] at hin
    constructor <;> omega

theorem call_scratch_bytes {target : RamState → BitVec 64} {ret : BitVec 64}
    (state : FrameState s t) (effect : (callEffect target ret t).Holds t u) :
    ∀ i < 64, u.external[scratch s + BitVec.ofNat 64 i]? =
      t.external[scratch s + BitVec.ofNat 64 i]? := by
  intro i hi
  apply effect.agrees.byte
  intro c hc ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · obtain ⟨j, hj, heq⟩ := ha
    have hap : OffsetsApart (-8) 8 0 64 := by unfold OffsetsApart; decide +kernel
    apply hap.ne (scratch s) hj hi (by decide)
    simpa [pushAddr, state.rsp, BitVec.sub_eq_add_neg] using heq.symm
  · exact ha.elim

theorem reduction_stage_at (square : Bool) {value : Nat} (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (rip : t.RIP = (if square then 0x11387d else 0x11390d))
    (left : t.regValue .rsi = scratch s) (right : t.regValue .rdx = scratch s + 32)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (bytes : Bytes t.external (scratch s) 64 (fun i => UInt8.ofNat (value / 256^i % 256)))
    (bound : value < p * 2^256) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = (if square then 0x113882 else 0x113912) ∧
      Nat256At u (s.regValue .rdi)
        (subtractP (reduceFour value)) := by
  obtain ⟨entered, callRun, ready, effect⟩ := call_reduction square pre state rip
  have saved := call_state pre state ready effect
  have hsp : stackPtr entered = stackPtr s - 144 := effect.writes.1.trans (call_address state)
  have hleft : entered.regValue .rsi = scratch s :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans left
  have hright : entered.regValue .rdx = scratch s + 32 :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans right
  have hdst : entered.regValue .rdi = s.regValue .rdi :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans destination
  have hright' : entered.regValue .rdx = stackPtr s - 104 := by
    rw [hright]
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have calleePre := reduction_pre pre saved hsp hleft hright' hdst
    ⟨effect.rip, by change InProgram (stackTop entered); rw [(callEffect_stack effect).1]; cases square <;> first | exact inProgram_of_textOffset 0x13912 (by decide) | exact inProgram_of_textOffset 0x13882 (by decide)⟩
  have hbytes : Bytes entered.external (scratch s) 64
      (fun i => UInt8.ofNat (value / 256^i % 256)) :=
    fun i hi => (call_scratch_bytes state effect i hi).trans (bytes i hi)
  have hlow : Nat256At entered (entered.regValue .rsi) (value % 2^256) := by
    rw [hleft]
    exact low_nat256 hbytes
  have hhigh : Nat256At entered (entered.regValue .rdx) (value / 2^256) := by
    rw [hright]
    exact high_nat256 hbytes (Nat.lt_trans bound
      (Nat.mul_lt_mul_of_pos_right p_lt_radix (by decide)))
  have hbound : value % 2^256 + 2^256 * (value / 2^256) < p * 2^256 := by
    rwa [Nat.mod_add_div]
  obtain ⟨final, result, output⟩ := reduction_correct calleePre hlow hhigh hbound
  have saved' := saved.after_result pre result (reduction_work_frame pre hsp hdst result)
  have finalSp : stackPtr final = scratch s := by
    change final.regValue .rsp = scratch s
    rw [result.rsp]
    exact (callEffect_stack effect).2.trans state.rsp
  have finalBx : final.regValue .rbx = s.regValue .rdi :=
    (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (r := 3) (n := 64) (by simp)).trans state.rbx)
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨1+fuel, final, callRun.trans run, ⟨saved', finalSp, finalBx⟩,
    result.rip.trans (callEffect_stack effect).1, ?_⟩
  simpa only [hdst, Nat.mod_add_div] using output


theorem reduction_stage {value : Nat} (pre : MultiplyPre s boundary)
    (state : FrameState s t) (rip : t.RIP = 0x11390d)
    (left : t.regValue .rsi = scratch s) (right : t.regValue .rdx = scratch s + 32)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (bytes : Bytes t.external (scratch s) 64 (fun i => UInt8.ofNat (value / 256^i % 256)))
    (bound : value < p * 2^256) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x113912 ∧
      Nat256At u (s.regValue .rdi)
        (subtractP (reduceFour value)) := by
  exact reduction_stage_at false pre.toCalleePre state rip left right destination bytes bound

end P256.Proofs.Field.Montgomery.Wrapper
