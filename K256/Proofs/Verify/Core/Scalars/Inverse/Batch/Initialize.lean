import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State
import K256.Proofs.Generate.Generator.Multiply.Split.Parameters
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert (value)

private theorem scalarWordsValue (s : Nat) (bound : s < 2^256) : value (scalarWords s) = s := by
  let w := scalarWords s
  have eq : w[0].toNat + 2^64 * (w[1].toNat + 2^64 *
      (w[2].toNat + 2^64 * w[3].toNat)) = s :=
    Generate.Generator.Multiply.Split.scalarWords_value s bound
  change (w[3].toNat * 2^64 + w[2].toNat) * 2^128 + w[1].toNat * 2^64 + w[0].toNat = s
  omega

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4096 in
theorem initializeLoop {a : Registers} {m : Ram} {sp : Word} {s : Nat} (h : Entry a m sp s) :
    ∃ b p, Reaches .l109490 a m .l1097fe b p ∧ LoopState a m sp s 0 b p 0 1 := by
  have rsp := congrArg (Value.get 64) h.rsp
  have rdi := congrArg (Value.get 64) h.rdi
  simp only [Value.get_mk_setWidth, BitVec.setWidth_eq] at rsp rdi
  have rcx := h.invWord
  have rdx := h.modPtr
  have rsi := h.scalarPtr
  have r8 := h.onePtr
  have stack := h.stack
  have low := h.depthBound
  have high := h.high
  have source := h.source
  have modulus := Generate.Generator.Multiply.Split.parameterAt h.image
    (p := 0x2021a0) (x := domain.n) (by decide +kernel)
  have unit := Generate.Generator.Multiply.Split.parameterAt h.image
    (p := 0x202180) (x := 1) (by decide +kernel)
  have modulusRead := modulus.readable
  have unitRead := unit.readable
  have modulusApart := (modulus.apart stack (by decide)).symm
  have unitApart := (unit.apart stack (by decide)).symm
  have f0 : memLoad m 0x2021a0 64 = (scalarWords domain.n)[0] := modulus.words 0 (by decide)
  have f1 : memLoad m 0x2021a8 64 = (scalarWords domain.n)[1] := modulus.words 1 (by decide)
  have f2 : memLoad m 0x2021b0 64 = (scalarWords domain.n)[2] := modulus.words 2 (by decide)
  have f3 : memLoad m 0x2021b8 64 = (scalarWords domain.n)[3] := modulus.words 3 (by decide)
  have g0 := h.input 0 (by decide)
  have g1 := h.input 1 (by decide)
  have g2 := h.input 2 (by decide)
  have g3 := h.input 3 (by decide)
  have u0 : memLoad m 0x202180 64 = (scalarWords 1)[0] := unit.words 0 (by decide)
  have u1 : memLoad m 0x202188 64 = (scalarWords 1)[1] := unit.words 1 (by decide)
  have u2 : memLoad m 0x202190 64 = (scalarWords 1)[2] := unit.words 2 (by decide)
  have u3 : memLoad m 0x202198 64 = (scalarWords 1)[3] := unit.words 3 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, Lift.reduceAddOffset] at g0 g1 g2 g3
  have inputValue := scalarWordsValue s (Nat.lt_trans h.bound (by decide +kernel))
  refine ⟨?initializedArgs, ?initializedRam, ?prologuePath, ?loopState⟩
  case prologuePath =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l109490, a, m⟩ =
        .jump ⟨.l1097fe, ?initializedArgs, ?initializedRam⟩ := by
      cfg_eval [rsp, rcx, rdx, rsi, rdi, r8, Lift.reduceAddOffset, Lift.reduceSubOffset,
        Lift.reduceAddNeg, Lift.reduceSubNeg, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l109490)
      segment_words [f0, f1, f2, f3, g0, g1, g2, g3, u0, u1, u2, u3]
      rfl
    refine .step (b := ⟨⟨.l1097fe, _, _⟩, []⟩) ?_ (Star.refl _)
    simp only [Program.sem, Program.step, run, Transfer.next]
  case loopState =>
    refine ⟨rfl, rfl, rfl, ?kept, ?saved, ?frame,
      ⟨scalarWords domain.n, false, ?fWords, ?fSign, ?fValue⟩,
      ⟨scalarWords s, false, ?gWords, ?gSign, congrArg Int.ofNat inputValue.symm⟩,
      ⟨#v[0, 0, 0, 0], false, ?dWords, ?dSign, by decide +kernel⟩,
      ⟨scalarWords 1, false, ?eWords, ?eSign, by decide +kernel⟩,
      ?dBound, ?eBound, ?dInvariant, ?eInvariant, ?originalNonzero, ?outputPtr, ?modulusPtr,
      ?modulusInverse⟩
    case kept =>
      intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    case saved =>
      intro ⟨i, hi⟩ off hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (refine_norm []; rfl)
    case frame => slot_state region
    case fWords | gWords | dWords | eWords =>
      intro i hi
      have hp : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hp with rfl | rfl | rfl | rfl
      all_goals
        refine_norm [base, wordAddr, Nat.reduceMul, g0, g1, g2, g3] <;> (first | assumption | rfl)
    case fSign | gSign | dSign | eSign =>
      refine_norm [base]
      rfl
    case fValue =>
      change (domain.n : Int) = (value (scalarWords domain.n) : Int)
      decide +kernel
    case dBound => decide +kernel
    case eBound => decide +kernel
    case dInvariant =>
      change (0 * (s : Int)) % domain.n = (domain.n : Int) % domain.n
      simp only [Int.zero_mul, Int.zero_emod, Int.emod_self]
    case eInvariant =>
      change (1 * (s : Int)) % domain.n = (s : Int) % domain.n
      rw [Int.one_mul]
    case originalNonzero =>
      refine_norm [base, g0, g1, g2, g3]
      intro hz
      obtain ⟨h012, h3⟩ := BitVec.or_eq_zero_iff.mp hz
      obtain ⟨h01, h2⟩ := BitVec.or_eq_zero_iff.mp h012
      obtain ⟨h1, h0⟩ := BitVec.or_eq_zero_iff.mp h01
      have : s = 0 := by
        rw [← inputValue, value, h0, h1, h2, h3]
        rfl
      exact (Nat.ne_of_gt h.positive) this
    case outputPtr => refine_norm [base] <;> rfl
    case modulusPtr => refine_norm [base] <;> rfl
    case modulusInverse => refine_norm [base] <;> rfl

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
