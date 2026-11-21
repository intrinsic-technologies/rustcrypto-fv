import P256.Proofs.SignatureFromDer.Fixed.Decode
import P256.Proofs.SignatureFromDer.Fixed.Finish

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem signature_decode_bounded [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x109ac0 input.size 72 560)
    (length : s.regValue .rdx = BitVec.ofNat 64 input.size)
    (bytes : (registerRegion s .rsi input.size).HasBytes s.external input) :
    ∃ t, CalleeResult s t boundary 72 560 ∧ ResultAt t (s.regValue .rdi) input := by
  by_cases size : input.size = 64
  · have pre' : CalleePre s boundary 0x109ac0 64 72 560 := by simpa only [size] using pre
    have bytes' : (registerRegion s .rsi 64).HasBytes s.external input := by
      simpa only [size] using bytes
    have length' : s.regValue .rdx = 64 := by simpa only [size, BitVec.ofNat_eq_ofNat] using length
    obtain ⟨t, rejected | decoded⟩ := signature_decode_components pre' length' bytes'
    · exact fixed_reject pre' rejected.1 rejected.2.1 rejected.2.2
    · exact fixed_finish pre' size decoded
  · have length' : s.regValue .rdx ≠ 64 := by
      intro h
      have hb : (s.regValue .rsi).toNat + input.size < 2^32 := pre.inputBounded
      have hn : input.size % 2^64 = 64 := congrArg BitVec.toNat (length.symm.trans h)
      rw [Nat.mod_eq_of_lt (by omega)] at hn
      exact size hn
    obtain ⟨t, state, rip⟩ := Decode.prologue_reject pre length'
    obtain ⟨u, result, tag⟩ := Finish.reject pre state rip
    refine ⟨u, result, ?_⟩
    simpa only [ResultAt, Ecdsa.decodeSignature, size, ite_false] using tag

theorem signature_decode_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x109ac0 64 72 896)
    (length : s.regValue .rdx = 64)
    (bytes : (registerRegion s .rsi 64).HasBytes s.external input) :
    ∃ t, CalleeResult s t boundary 72 896 ∧ ResultAt t (s.regValue .rdi) input := by
  have subset (a : Nat) (ha : (Stack.region s 560).Contains a) :
      (Stack.region s 896).Contains a := by
    change (Stack.region s 560).start ≤ a ∧ a <
      (Stack.region s 560).start + (Stack.region s 560).size at ha
    change (Stack.region s 896).start ≤ a ∧ a <
      (Stack.region s 896).start + (Stack.region s 896).size
    rw [stack_region_end] at ha ⊢
    change (stackPtr s).toNat - 896 ≤ a ∧ a < (stackPtr s).toNat + 8
    change (stackPtr s).toNat - 560 ≤ a ∧ a < (stackPtr s).toNat + 8 at ha
    constructor <;> omega
  have pre' : CalleePre s boundary 0x109ac0 64 72 560 := by
    refine { pre with stack := ?_, separation := ?_, avoids := ?_ }
    · refine ⟨?_, fun a ha => pre.stack.2.1 a (subset _ ha), ?_, pre.stack.2.2.2⟩
      · change (Stack.region s 560).start + (Stack.region s 560).size < 2^32
        rw [stack_region_end]
        exact (stack_bounds pre.stack).2
      · have hb := (stack_bounds pre.stack).1
        change 560 ≤ (stackPtr s).toNat
        omega
    · have sub (i : Fin 3) (a : Nat)
          (ha : (#v[registerRegion s .rsi 64, registerRegion s .rdi 72,
            Stack.region s 560][i]).Contains a) :
          (#v[registerRegion s .rsi 64, registerRegion s .rdi 72,
            Stack.region s 896][i]).Contains a := by
        by_cases h0 : i = 0
        · subst i
          change (registerRegion s .rsi 64).Contains a at ha ⊢
          exact ha
        by_cases h1 : i = 1
        · subst i
          change (registerRegion s .rdi 72).Contains a at ha ⊢
          exact ha
        have h2 : i = 2 := Fin.ext (by have := i.isLt; simp only [Fin.ext_iff] at h0 h1; omega)
        subst i
        exact subset a ha
      exact fun i j hij a ha hb => pre.separation i j hij a (sub i a ha) (sub j a hb)
    · intro region hr a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact pre.avoids _ (by simp) a ha
      · exact pre.avoids _ (by simp) a (subset _ ha)
  have size : input.size = 64 := bytes.1
  obtain ⟨t, result, value⟩ := signature_decode_bounded (s := s) (boundary := boundary) (input := input) (by simpa only [size] using pre')
    (by simpa only [size, BitVec.ofNat_eq_ofNat] using length) (by simpa only [size] using bytes)
  refine ⟨t, { result with frame := ?_ }, value⟩
  intro a ha
  apply result.frame a
  intro region hr hin
  have h : region = registerRegion s .rdi 72 ∨ region = Stack.region s 560 := by simpa using hr
  rcases h with rfl | rfl
  · exact ha _ (by simp) hin
  · exact ha _ (by simp) (subset _ hin)

end P256.Proofs.SignatureFromDer.Fixed
