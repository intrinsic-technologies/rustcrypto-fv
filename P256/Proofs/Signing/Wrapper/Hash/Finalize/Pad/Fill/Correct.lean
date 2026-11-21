import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill.Call
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill.Memory
import P256.Proofs.HMAC.Finalize.Padding.Bytes
import P256.Proofs.HMAC.Finalize.Copy
import P256.Proofs.Program.Fill

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fill [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Marked initial start s message) :
    ∃ t, Padded initial start t message := by
  obtain ⟨u, callRun, _, effect, frame⟩ := Fill.call pre state
  have base : frameBase initial + 64 = stackPtr initial - 456#64 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have dst : u.regValue .rdi = (frameBase initial + 64) + BitVec.ofNat 64 (message.size % 64 + 1) :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans (by
      change s.regValue .rdi = _
      rw [state.destination]
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      change frameBase initial + (BitVec.ofNat 64 (message.size % 64) + (64#64 + 1#64)) = _
      ac_rfl)
  have dst' : u.regValue .rdi = stackPtr initial - 456#64 + BitVec.ofNat 64 (message.size % 64 + 1) := by
    rw [← base]
    exact dst
  have zero : u.regValue .rsi = 0 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.zero
  have count : u.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64) :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.length
  have callPre := Fill.callee_pre pre frame effect.rip dst' zero (by
    change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0x2895 (by decide))
  obtain ⟨t, result, zeros, _⟩ := Program.memset_zero_correct callPre
    (by rw [zero]; rfl) count (by omega)
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have destination : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (455 - message.size % 64) := by
    rw [dst']
    bv_omega
  have finalFrame : Frame initial start t :=
    frame.after_callee pre.context result destination (by decide) (by decide)
      (by omega) (by omega)
  have saved (r : Syntax.Reg) (member : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = s.regValue r := by
    apply (result.calleeSaved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have bytes (i : Nat) (hi : i < 288) (outside : i ≤ message.size % 64 ∨ 64 ≤ i) :
      t.external[(frameBase initial + 64) + BitVec.ofNat 64 i]? =
        s.external[(frameBase initial + 64) + BitVec.ofNat 64 i]? := by
    rw [base]
    exact (Fill.result_byte pre frame.rsp dst' result hi outside).trans
      (ScalarFrame.call_byte (frameOffset := 520) (by decide)
        state.rsp effect (offset := 456) (len := 288) (by decide) (by decide) hi)
  refine ⟨t, {
    toLive := ⟨finalFrame⟩
    rip := result.rip.trans (callEffect_stack effect).1
    hash := ?_
    buffer := ?_
    hashPointer := (saved .r15 (by simp)).trans state.hashPointer
    count := (saved .r14 (by simp)).trans state.count
    position := (saved .rbx (by simp)).trans state.position
    remaining := (saved .r12 (by simp)).trans state.remaining }⟩
  · have hh : SHA256.HashStateAt s (frameBase initial + 64 + 64)
        (SHA256.compressBlocks SHA256.initialHash message) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using state.hash
    have normalize : frameBase initial + 64 + 64 = frameBase initial + 128 := by
      rw [BitVec.add_assoc]
      rfl
    rw [← normalize]
    apply hh.copy
    intro i hi
    have h := bytes (64 + i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using h
  · apply SHA256.padded_bytes
    · exact hasBytes_copy state.tail (fun i hi => bytes i (by omega) (.inl (by omega)))
    · exact (bytes _ (by omega) (.inl (Nat.le_refl _))).trans state.marker
    · intro i hi
      have h := zeros i hi
      simpa only [dst, BitVec.add_assoc, ← BitVec.ofNat_add] using h

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad
