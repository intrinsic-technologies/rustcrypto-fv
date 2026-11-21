import P256.Proofs.Sec1.Decode.Prepare.Prefix.Call
import P256.Proofs.Program.Fill

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t v u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}

omit [Bindings] in
theorem buffer_offset (s : RamState) {n : Nat} (bound : n ≤ 312) :
    stackPtr s - BitVec.ofNat 64 (312 - n) = stackPtr s - 312#64 + BitVec.ofNat 64 n := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 312 n (by omega) bound]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem memory_callee_saved {target ret : BitVec 64} {count : Nat}
    (effect : (callEffect (fun _ ↦ target) ret t).Holds t v)
    (result : CalleeResult v u boundary count 0) (r : Syntax.Reg)
    (member : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) : u.regValue r = t.regValue r := by
  apply (result.calleeSaved r member).trans
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact effect.agrees.read (n := 64) (r := 3) (by simp)
  · exact effect.agrees.read (n := 64) (r := 5) (by simp)
  · exact effect.agrees.read (n := 64) (r := 12) (by simp)
  · exact effect.agrees.read (n := 64) (r := 13) (by simp)
  · exact effect.agrees.read (n := 64) (r := 14) (by simp)
  · exact effect.agrees.read (n := 64) (r := 15) (by simp)

theorem fill (pre : DecodePre s boundary bytes) (state : Frame s t)
    (shape : EncodingShape bytes) (rip : t.RIP = 0x10e54c)
    (destination : t.regValue .rdi = stackPtr s - 312#64 + BitVec.ofNat 64 bytes.size)
    (zero : t.regValue .rsi = 0) (count : t.regValue .rdx = BitVec.ofNat 64 (65 - bytes.size)) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10e552 ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) ∧
      (∀ i < 65, bytes.size ≤ i → u.external[stackPtr s - 312#64 + BitVec.ofNat 64 i]? = some 0) := by
  have bound : bytes.size ≤ 65 := by have := shape.size; omega
  obtain ⟨v, runV, ready, effect⟩ := memory_call false pre state rip
  have sp : stackPtr v = stackPtr s - 320#64 := effect.writes.1.trans (push_address state)
  have dst : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 (312 - bytes.size) := by
    rw [buffer_offset s (by omega)]
    exact (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have si : v.regValue .rsi = 0 := (effect.agrees.read (n := 64) (r := 6) (by simp)).trans zero
  let layout : StackBufferLayout 3680 (65 - bytes.size) 0 :=
    ⟨320,312-bytes.size,by decide,by decide,by omega,by omega⟩
  have child : CalleePre v boundary 0x11c810 0 (65 - bytes.size) 0 := by
    apply CalleePre.of_disjoint_input_and_stack layout pre.stack (pre.avoids _ (by simp))
      (bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees)
      (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
      (effect.agrees.directionFlagClear (by simp) state.directionFlag)
      (push_loaded pre state effect) effect.rip sp
    · change (v.regValue .rsi).toNat + 0 < 2^32
      rw [si]; decide
    · intro a ha
      change (v.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (v.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha _
      change (v.regValue .rsi).toNat ≤ a ∧ a < (v.regValue .rsi).toNat + 0 at ha
      omega
    · exact dst
    · exact fun a ha ↦ effect.agrees.grow a (state.allocated a ha)
    · exact pre.outerBoundary
    · change InProgram (stackTop v)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0xe552 (by decide)
  obtain ⟨u, result, zeros, _⟩ := memset_zero_correct child (by rw [si]; rfl)
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by omega)
  obtain ⟨n, runU⟩ := result.execution
  refine ⟨1+n,u,runV.trans runU,after_callee pre state effect result
    (result_memory pre state effect dst (by omega) (by omega) result),
    result.rip.trans (callEffect_stack effect).1, memory_callee_saved effect result, ?_⟩
  intro i hi hsize
  have h := zeros (i-bytes.size) (by omega)
  rw [dst, buffer_offset s (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    Nat.add_sub_of_le hsize] at h
  exact h

end P256.Proofs.Sec1.Decode.Prepare
