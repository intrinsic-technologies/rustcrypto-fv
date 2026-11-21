import P256.Proofs.Projective.Multiply.Machine.Radix.Digits
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix
open Recenter (rawDigit)

theorem byteOffset_signExtend {n : Nat} (h : n < 128) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    simp only [BitVec.toNat_ofNat]
    omega

def extractionComponents (s : RamState) (start len : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .flags,
    .mem (stackPtr s - 112 + BitVec.ofNat 64 start) len, .rip]

theorem extraction_agrees {s t u : RamState} {start len : Nat} (bound : start + len ≤ 65)
    (h : AgreesExcept (extractionComponents s start len) t u) :
    AgreesExcept (digitComponents s) t u := by
  apply h.widen
  · intro c hc hm
    simp only [extractionComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [digitComponents, Component.isMem]
  · intro a c hc covered
    simp only [extractionComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,he⟩ := covered
    refine ⟨.mem (stackPtr s - 112) 65, by simp [digitComponents], start+j, by omega, ?_⟩
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem extraction_unchanged {s t u : RamState} {start len i : Nat}
    (bound : start + len ≤ 65) (hi : i < 65) (apart : i < start ∨ start + len ≤ i)
    (h : AgreesExcept (extractionComponents s start len) t u) :
    (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 i) : Operand 8).read u =
      (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 i) : Operand 8).read t := by
  apply memLoad_congr
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simp only [BitVec.add_zero]
  change (u.external[stackPtr s - 112 + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - 112 + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte]
  intro c hc covered
  simp only [extractionComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j,hj,he⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_right_inj] at he
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show start+j < 2^64 by omega)] at hn
  omega

structure ExtractionState [Bindings] (s t : RamState) (d n : Nat) : Prop extends State s t where
  encoded : X86Proofs.Bytes t.external (stackPtr s - 40) 32
    (fun i => UInt8.ofNat (d / 256 ^ (31-i) % 256))
  digits : BytesAt t (stackPtr s - 112) (2*n) (rawDigit d)
  last : (Operand.mem (stackPtr s - 48) : Operand 8).read t = 0
  rax : 0 < n → (Operand.reg 0 : Operand 8).read t = BitVec.ofNat 8 (nibble d 0)

theorem ExtractionState.after [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {d n k : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : ExtractionState s t d n) (bound : n+k ≤ 32)
    (ready : ReadyToStep u) (agrees : AgreesExcept (extractionComponents s (2*n) (2*k)) t u)
    (digits : ∀ i, 2*n ≤ i → i < 2*(n+k) →
      (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 i) : Operand 8).read u = rawDigit d i)
    (rax : 0 < n+k → (Operand.reg 0 : Operand 8).read u = BitVec.ofNat 8 (nibble d 0)) :
    ExtractionState s u d (n+k) := by
  have full := extraction_agrees (by omega) agrees
  refine ⟨frame_after_digits pre state.toState ready full, ?_, ?_, ?_, rax⟩
  · intro i hi
    exact (digit_byte pre full (offset := 40) (len := 32) (by decide) (by decide) (by omega) hi).trans (state.encoded i hi)
  · intro i hi
    by_cases old : i < 2*n
    · exact (extraction_unchanged (by omega) (by omega) (.inl old) agrees).trans (state.digits i old)
    · exact digits i (by omega) hi
  · have h := extraction_unchanged (i := 64) (by omega) (by decide) (.inr (by omega)) agrees
    have addr : stackPtr s - 112 + BitVec.ofNat 64 64 = stackPtr s - 48 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [addr] at h
    exact h.trans state.last

theorem ExtractionState.byte [Bindings] {s t : RamState} {d n i : Nat}
    (state : ExtractionState s t d n) (hi : i < 32) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 (111-i)) : Operand 8).read t =
      BitVec.ofNat 8 (d / 256 ^ i % 256) := by
  have addr : stackPtr t + BitVec.ofNat 64 (111-i) =
      stackPtr s - 40 + BitVec.ofNat 64 (31-i) := by
    rw [state.rsp]
    rw [show 111-i = 80+(31-i) by omega,BitVec.ofNat_add,← BitVec.add_assoc]
    congr 1
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hb := state.encoded.loadByte (31-i) (by omega)
  rw [show 31-(31-i) = i by omega] at hb
  rw [addr]
  exact hb

end P256.Proofs.Projective.Multiply.Machine.Radix
