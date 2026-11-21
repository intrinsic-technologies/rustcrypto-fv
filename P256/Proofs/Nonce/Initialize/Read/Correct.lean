import P256.Proofs.Nonce.Initialize.Read.Frame
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Nonce.Initialize.Prepare

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Read

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure Decoded [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
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
  shift : s.regValue .rbp = 0
  status : (Operand.reg 0 : Operand 8).read s = 255
  value : Nat256At s (stackPtr s + 104) (Arith.uint digest)

set_option maxRecDepth 2000 in
theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (state : Prepare.CallReady initial s boundary) (rip : s.RIP = 0x107955)
    (bytes : (registerRegion initial .rcx 32).HasBytes initial.external digest) :
    ∃ t, Decoded initial t boundary digest ∧ t.RIP = 0x10795a := by
  obtain ⟨entry, ef, cp, eb, effect⟩ := call pre state rip bytes
  have dst : entry.regValue .rdx = stackPtr initial - 176 := by
    have h := (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.outputPointer
    change entry.regValue .rdx = stackPtr s + 104 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  obtain ⟨t, result⟩ := ReadBe.read_be_correct cp eb
  have tf := result_frame pre ef result dst
  have st : stackPtr t = stackPtr s := by rw [tf.rsp, state.stage.rsp]
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr initial).toNat - 288 := by
    rw [ef.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dn : (entry.regValue .rdx).toNat = (stackPtr initial).toNat - 176 := by
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
      have cases : region = registerRegion entry .rdx 32 ∨ region = Stack.region entry 128 := by
        simpa using member
      rcases cases with rfl | rfl
      · change (entry.regValue .rdx).toNat ≤ _ ∧ _ < (entry.regValue .rdx).toNat + 32 at inside
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
  refine ⟨t, ⟨tf, (word 192 (by decide) (by decide)).trans state.output,
    (word 184 (by decide) (by decide)).trans state.secret,
    (word 176 (by decide) (by decide)).trans state.length,
    (word 168 (by decide) (by decide)).trans state.entropy,
    (reg .r15 (by simp)).trans state.order0,
    (reg .r14 (by simp)).trans state.order1,
    (reg .r13 (by simp)).trans state.order2,
    (reg .rbx (by simp)).trans state.order3,
    (reg .rbp (by simp)).trans state.shift, result.status, ?_⟩,
    result.rip.trans (callEffect_stack effect).1⟩
  have out : stackPtr t + 104 = stackPtr initial - 176 := by
    rw [tf.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [out]
  apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs
  · have hsize : digest.size = 32 := bytes.1
    simpa only [Arith.uint, Arith.decodeBigEndian, hsize,
      show (256 : Nat)^32 = 2^256 by decide +kernel] using
      SecretKeyFromBytes.Encoding.octetsToNat_lt digest
  · intro i hi
    exact tf.allocated _ ((stack_sub_readable pre.stack (offset := 176) (len := 32)
      (by decide) (by decide)).mem i hi)
  · exact dst ▸ result.value

end P256.Proofs.Nonce.Initialize.Read
