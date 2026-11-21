import P256.Proofs.Nonce.Initialize.Shift.Call
import P256.Proofs.Program.FieldCall.Result

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Shift

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure ReducedInput [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (digest : ByteArray) : Prop where
  stage : Stage initial s boundary
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  length : memLoad s.external (stackPtr s + 176) 64 = 32
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  order0 : s.regValue .r15 = 0xf3b9cac2fc632551
  order1 : s.regValue .r14 = 0xbce6faada7179e84
  order2 : s.regValue .r13 = 0xffffffffffffffff
  order3 : s.regValue .rbx = 0xffffffff00000000
  value : Nat256At s (stackPtr s + 8) (Arith.uint digest)

theorem result [Bindings] {initial s entry t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (state : Read.ShiftReady initial s boundary digest)
    (entryFrame : Stage initial entry boundary 288)
    (effect : (callEffect (fun _ => 0x109530) 0x10799e s).Holds s entry)
    (result : CalleeResult entry t boundary 32 128)
    (value : Nat256At t (entry.regValue .rdi) (Arith.uint digest)) :
    ReducedInput initial t boundary digest ∧ t.RIP = 0x10799e := by
  have dst : entry.regValue .rdi = stackPtr initial - 272 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.destination
    change entry.regValue .rdi = stackPtr s + 8 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have memory := FieldCall.stack_result_work_frame (frameOffset := 280) pre.toCalleePre
    entryFrame.toFrameState result dst (by decide) (by decide) (by decide) (by decide)
  have tf : Stage initial t boundary := by
    obtain ⟨n, hn⟩ := entryFrame.execution
    obtain ⟨m, hm⟩ := result.execution
    exact ⟨FieldCall.after_result pre.toCalleePre entryFrame.toFrameState result (by decide) memory,
      n + m, hn.trans hm⟩
  have st : stackPtr t = stackPtr s := by rw [tf.rsp, state.stage.rsp]
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr initial).toNat - 288 := by
    rw [entryFrame.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dn : (entry.regValue .rdi).toNat = (stackPtr initial).toNat - 272 := by
    rw [dst]
    exact stack_sub_toNat pre.stack (by decide)
  have word (offset : Nat) (lo : 168 ≤ offset) (hi : offset + 8 ≤ 200) :
      memLoad t.external (stackPtr t + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
    rw [st]
    apply memLoad_congr
    intro i hin
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    congr 1
    have address : stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
        stackPtr initial - BitVec.ofNat 64 (280 - (offset + i)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact HMAC.Finalize.stack_address (depth := 280) state.stage.rsp (by omega)
    have an : (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - (280 - (offset + i)) := by
      rw [address]
      exact stack_sub_toNat pre.stack (by omega)
    rw [result.frame _]
    · rw [address]
      simpa only [BitVec.add_zero] using
        ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide) state.stage.toFrameState effect
          (offset := 280 - (offset + i)) (len := 1) (by omega) (by omega) (i := 0) (by decide)
    · intro region member inside
      have cases : region = registerRegion entry .rdi 32 ∨ region = Stack.region entry 128 := by
        simpa using member
      rcases cases with rfl | rfl
      · change (entry.regValue .rdi).toNat ≤ _ ∧ _ < (entry.regValue .rdi).toNat + 32 at inside
        rw [dn, an] at inside
        omega
      · have high := inside.2
        rw [stack_region_end] at high
        change _ < (stackPtr entry).toNat + 8 at high
        rw [sp, an] at high
        omega
  have reg (r : Syntax.Reg) (hr : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = s.regValue r := by
    refine (result.calleeSaved r hr).trans ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp [pushEffect_components])
    · exact effect.agrees.read (n := 64) (r := 5) (by simp [pushEffect_components])
    · exact effect.agrees.read (n := 64) (r := 12) (by simp [pushEffect_components])
    · exact effect.agrees.read (n := 64) (r := 13) (by simp [pushEffect_components])
    · exact effect.agrees.read (n := 64) (r := 14) (by simp [pushEffect_components])
    · exact effect.agrees.read (n := 64) (r := 15) (by simp [pushEffect_components])
  refine ⟨⟨tf, (word 192 (by decide) (by decide)).trans state.output,
    (word 184 (by decide) (by decide)).trans state.secret,
    (word 176 (by decide) (by decide)).trans state.length,
    (word 168 (by decide) (by decide)).trans state.entropy,
    (reg .r15 (by simp)).trans state.order0,
    (reg .r14 (by simp)).trans state.order1,
    (reg .r13 (by simp)).trans state.order2,
    (reg .rbx (by simp)).trans state.order3, ?_⟩,
    result.rip.trans (callEffect_stack effect).1⟩
  have out : stackPtr t + 8 = stackPtr initial - 272 := by
    rw [tf.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rwa [out, ← dst]

end P256.Proofs.Nonce.Initialize.Shift
