import P256.Proofs.Nonce.Initialize.Seed.SerializeCall.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Serialized [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) (value : Nat) : Prop where
  stage : Stage initial s boundary
  rip : s.RIP = 0x107b85
  order : s.regValue .r15 = orderAddress
  buffer : s.regValue .r12 = stackPtr s + 200
  length : s.regValue .rbx = 32
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  outputPointer : s.regValue .r14 = initial.regValue .rdi
  octets : ({ start := (stackPtr s + 200).toNat, size := 32 } : MemoryRegion).HasBytes s.external
    (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n value)

theorem serialization_result [Bindings] {initial s entry t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {value : Nat}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (state : SerializationReady initial s boundary orderAddress value)
    (entryFrame : Stage initial entry boundary 288)
    (effect : (callEffect (fun _ => 0x106f40) 0x107b85 s).Holds s entry)
    (result : Conversions.Int2Octets.Result entry t boundary value) :
    Serialized initial t boundary orderAddress value := by
  have dst : entry.regValue .rdx = stackPtr initial - 80 := by
    have h := (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.destination
    change entry.regValue .rdx = stackPtr s + 200 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have tf := serialization_result_frame pre entryFrame result dst
  have st : stackPtr t = stackPtr s := by rw [tf.rsp, state.stage.rsp]
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr initial).toNat - 288 := by
    rw [entryFrame.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dn : (entry.regValue .rdx).toNat = (stackPtr initial).toNat - 80 := by
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
  refine {
    stage := tf
    rip := result.rip.trans (callEffect_stack effect).1
    order := (reg .r15 (by simp)).trans state.order
    buffer := by simpa only [st] using (reg .r12 (by simp)).trans state.buffer
    length := (reg .rbx (by simp)).trans state.length
    secret := (word 184 (by decide) (by decide)).trans state.secret
    output := (word 192 (by decide) (by decide)).trans state.output
    entropy := (word 168 (by decide) (by decide)).trans state.entropy
    outputPointer := (reg .r14 (by simp)).trans state.outputPointer
    octets := ?_
  }
  have out : stackPtr t + 200 = entry.regValue .rdx := by
    rw [dst, tf.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  simpa only [out, registerRegion] using result.output

end P256.Proofs.Nonce.Initialize.Seed
