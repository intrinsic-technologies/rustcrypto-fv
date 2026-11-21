import P256.Proofs.SignatureFromDer.Model
import P256.Proofs.SignatureFromDer.Fixed.Decode.Prologue
import P256.Proofs.SignatureFromDer.Fixed.Decode.Copies
import P256.Proofs.SignatureFromDer.Fixed.Decode.ScalarCall
import P256.Proofs.SignatureFromDer.Fixed.Decode.CheckedScalar

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program (CalleePre)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.SignatureFromDer.Fixed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem signature_decode_components [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x109ac0 64 72 560)
    (length : s.regValue .rdx = 64)
    (bytes : (registerRegion s .rsi 64).HasBytes s.external input) :
    ∃ t, (Stage s t boundary ∧ t.RIP = 0x109c57 ∧ Ecdsa.decodeSignature input = none) ∨
      DecodedState s t boundary input := by
  obtain ⟨a, ast⟩ := Decode.prologue pre length bytes
  obtain ⟨b, bst, bip, bb, bf⟩ := Decode.copy_argument pre ast.toStage false ast.rip ast.rsi bytes
  simp only [Bool.false_eq_true, ite_false] at bip bb bf
  obtain ⟨c, cst, cip, cr, c14, _⟩ := Decode.call_scalar pre bst false bip bb
  simp only [Bool.false_eq_true, ite_false] at cip cr
  obtain ⟨d, dst, dip, dr, df⟩ := Decode.scalar_status pre cst false cip cr
  simp only [Bool.false_eq_true, ite_false] at dip dr
  by_cases first : Arith.uint (input.extract 0 32) < Operations.domain.n
  · have dstart : d.RIP = 0x109b1c := by simpa only [first, ite_true, Bool.false_eq_true, ite_false] using dip
    obtain ⟨e, est, eip, er, ef⟩ := Decode.save_scalar pre dst false dstart (dr first)
    simp only [Bool.false_eq_true, ite_false] at eip er ef
    have e14 : e.regValue .r14 = s.regValue .rsi :=
      (ef.read (n := 64) (r := 14) (by simp [Decode.Copy.Result.components])).trans
        ((df.read (n := 64) (r := 14) (by simp)).trans
          (c14.trans ((bf.read (n := 64) (r := 14) (by simp [Copy32.components])).trans ast.r14)))
    obtain ⟨f, fst, fip, fb, ff⟩ := Decode.copy_argument pre est true eip e14 bytes
    simp only [ite_true] at fip fb ff
    have fsp : stackPtr f = stackPtr e := ff.read (n := 64) (r := 4) (by simp [Copy32.components])
    have fr : Nat256At f (stackPtr f + 104) (Arith.uint (input.extract 0 32)) := by
      rw [fsp]
      apply Decode.copy_preserves_nat256 ff _ er
      exact RangeApart.offsets (stackPtr e) (a := 72) (b := 104)
        (by decide) (by decide) (.inl (by decide))
    obtain ⟨g, gst, gip, gr, _, gp⟩ := Decode.call_scalar pre fst true fip fb
    simp only [ite_true] at gip gr gp
    have grfirst : Nat256At g (stackPtr g + 104) (Arith.uint (input.extract 0 32)) :=
      ⟨fr.1, fun i hi => (gp 104 32 i (by decide) (by decide) hi).trans (fr.2 i hi)⟩
    obtain ⟨h, hst, hip, hr, hf⟩ := Decode.scalar_status pre gst true gip gr
    simp only [ite_true] at hip hr
    by_cases second : Arith.uint (input.extract 32 64) < Operations.domain.n
    · have hstart : h.RIP = 0x109b8a := by simpa only [second, ite_true] using hip
      have hmemory := hf.external (by simp [Component.Covers])
      have hsp : stackPtr h = stackPtr g := hf.read (n := 64) (r := 4) (by simp)
      have hrfirst : Nat256At h (stackPtr h + 104) (Arith.uint (input.extract 0 32)) := by
        simpa only [Nat256At, hmemory, hsp] using grfirst
      obtain ⟨u, ust, uip, ur, uf⟩ := Decode.save_scalar pre hst true hstart (hr second)
      simp only [ite_true] at uip ur uf
      have usp : stackPtr u = stackPtr h := uf.read (n := 64) (r := 4) (by simp [Decode.Copy.Result.components])
      have urfirst : Nat256At u (stackPtr u + 104) (Arith.uint (input.extract 0 32)) := by
        rw [usp]
        refine ⟨hrfirst.1, fun i hi => Eq.trans (uf.byte ?_) (hrfirst.2 i hi)⟩
        intro c hc ha
        simp only [Decode.Copy.Result.components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        all_goals try exact ha.elim
        obtain ⟨j,hj,he⟩ := ha
        exact RangeApart.offsets (stackPtr h) (a := 136) (b := 104)
          (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
      exact ⟨u, .inr ⟨ust, uip, urfirst, ur, first, second⟩⟩
    · refine ⟨h, .inl ⟨hst, ?_, ?_⟩⟩
      · simpa only [second, ite_false] using hip
      · exact (decodeSignature_none_iff bytes.1).2 (.inr (.inr (.inr (Nat.le_of_not_gt second))))
  · refine ⟨d, .inl ⟨dst, ?_, ?_⟩⟩
    · simpa only [first, ite_false] using dip
    · exact (decodeSignature_none_iff bytes.1).2 (.inr (.inl (Nat.le_of_not_gt first)))

end P256.Proofs.SignatureFromDer.Fixed
