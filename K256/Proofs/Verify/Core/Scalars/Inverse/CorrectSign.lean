import K256.Proofs.Common.Invert.Correct
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.Generator.Multiply.Split.Parameters

namespace K256.Proofs.Verify.Core.Scalars.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field Verify.LIR
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult SignedSource)
open Generate.Generator.Affine.Invert (value)
open Generate.Generator.Multiply (scalarWords)
open Standards.SECG.DomainParameters.Secp256k1

private theorem correctionMask (v : Vector (BitVec 64) 4) (flag : Value) (sign : BitVec 8) :
    -(((if (orFlags (v[1] ||| v[0] ||| v[2] ||| v[3])).ZF.getD false = true then (0 : BitVec 32)
         else ((mergeGPR 8 (((mergeGPR 8 ((flag.get 64).setWidth 8 ^^^ sign) (flag.get 64)).setWidth 8) &&& 1)
              (mergeGPR 8 ((flag.get 64).setWidth 8 ^^^ sign) (flag.get 64))).setWidth 8).setWidth 32).setWidth 8).setWidth 64) =
      Common.Invert.Correct.signMask v (flag.get 8) sign := by
  have zf : (orFlags (v[1] ||| v[0] ||| v[2] ||| v[3])).ZF.getD false = true ↔ Common.Invert.Correct.magnitudeOr v = 0 :=
    beq_iff_eq
  simp only [setWidth_mergeGPR8, setWidth_get flag (by decide : 8 ≤ 64), zf, Common.Invert.Correct.signMask, Common.Invert.Correct.signBit]
  split
  · rfl
  · rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1500 in
theorem correctSign {a : Registers} {m : Ram} {sp dst ret : Word} {x : Int} (neg : Bool)
    (fr : CalleeFrame a m sp dst ret 56 32)
    (src : SignedSource m sp dst (a[6].get 64) 56 32 x)
    (ptr : a[1].get 64 = 0x2021a0)
    (flag : (a[2].get 8 &&& 1) = (if neg then 1 else 0)) (bound : x.natAbs < domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109c00, a, m⟩, []⟩ out ∧ CalleeResult a m sp dst ret 56 32 out ∧
      ∃ v : Vector Word 4, WordsAt out.store dst 64 v ∧
        value v = ((if neg then -x else x) % (domain.n : Int)).toNat := by
  obtain ⟨v, inputNeg, words, sign, signed⟩ := src.signed
  generalize hsource : a[6].get 64 = source at *
  have srcRead := src.read
  have depth := fr.depthBound
  have srcApart := src.stackApart
  have outApart := fr.apart
  have stack := fr.stack
  have output := fr.output
  have returnSlot := fr.returnSlot
  have retAddr := fr.retAddr
  have retLow := fr.retLow
  have stackLow := stack.readable.low
  have outLow := output.readable.low
  have spLow := returnSlot.low
  have rsp : a[4].get 64 = sp := by rw [fr.rsp]; rfl
  have rdi : a[7].get 64 = dst := by rw [fr.rdi]; rfl
  have stackStart : (sp - (56 : Word)).toNat = sp.toNat - 56 :=
    BitVec.toNat_sub_of_le (by exact depth)
  have table := Generate.Generator.Multiply.Split.parameterAt fr.image
    (p := 0x2021a0) (x := domain.n) (by decide +kernel)
  have modApart := (table.apart stack (by decide)).symm
  have r0 : Readable m 0x2021a0 8 := table.readable.sub (by decide) (by decide)
  have r1 : Readable m 0x2021a8 8 := table.readable.sub (by decide) (by decide)
  have r2 : Readable m 0x2021b0 8 := table.readable.sub (by decide) (by decide)
  have r3 : Readable m 0x2021b8 8 := table.readable.sub (by decide) (by decide)
  have w0 : memLoad m source 64 = v[0] := by
    simpa [wordAddr] using words 0 (by decide)
  have w1 : memLoad m (source + 8) 64 = v[1] := words 1 (by decide)
  have w2 : memLoad m (source + 16) 64 = v[2] := words 2 (by decide)
  have w3 : memLoad m (source + 24) 64 = v[3] := words 3 (by decide)
  have q0 : memLoad m 0x2021a0 64 = (scalarWords domain.n)[0] := table.words 0 (by decide)
  have q1 : memLoad m 0x2021a8 64 = (scalarWords domain.n)[1] := table.words 1 (by decide)
  have q2 : memLoad m 0x2021b0 64 = (scalarWords domain.n)[2] := table.words 2 (by decide)
  have q3 : memLoad m 0x2021b8 64 = (scalarWords domain.n)[3] := table.words 3 (by decide)
  have finishRun {o : Output Value Ram Reg.count}
      (run : program.runBlock (dialect Extracted.programImage) ⟨.l109c00, a, m⟩ = .returned o) :
      program.Exec (dialect Extracted.programImage) ⟨⟨.l109c00, a, m⟩, []⟩ o := by
    apply Program.Exec.done
    simp only [Program.step, run, Transfer.next]
  refine ⟨?out, finishRun ?run, ?post⟩
  case run =>
    cfg_eval [b_l109c00, b_l109c00_1, b_l109c00_2, b_l109c00_3, b_l109c00_4,
      b_l109c00_5, rsp, rdi, ptr, hsource, retAddr, w0, w1, w2, w3, q0, q1, q2, q3, sign]
    segment_words [rsp, rdi, ptr, hsource, retAddr, w0, w1, w2, w3, q0, q1, q2, q3, sign]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l109c00 | assumption)
    refine (ite_eq_left ⟨by slot_guard using code_l109c00, retLow⟩).trans ?_
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, ?kept, ?controls, ?frame⟩, ?words⟩
    case kept =>
      have eq64 (r : Value) (h : r.width = 64) : (⟨64, r.get 64⟩ : Value) = r := by
        obtain ⟨w, b⟩ := r
        change w = 64 at h
        subst w
        rfl
      intro ⟨i, hi⟩ hm hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact eq64 _ hw | rfl
    case controls =>
      intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl
    case frame =>
      dsimp only
      slot_state region
    case words =>
      let signByte : BitVec 8 := if inputNeg then 1 else 0
      let result := Common.Invert.Correct.correctedWords (scalarWords domain.n) v (a[2].get 8) signByte
      refine ⟨result, ?_, ?_⟩
      · dsimp only
        lifted_word_reads []
        all_goals rw [correctionMask]
        all_goals first | rfl | lifted_word_eq [Common.Invert.Correct.correctedWords]
      · have mag : x.natAbs = value v := by rw [signed]; cases inputNeg <;> simp
        have modulus_value : value (scalarWords domain.n) = domain.n := by decide +kernel
        have hb : value v < value (scalarWords domain.n) := by rwa [modulus_value, ← mag]
        have hv := Common.Invert.Correct.correctedWords_value (scalarWords domain.n) v (a[2].get 8) inputNeg neg flag hb
        dsimp only at hv
        rw [modulus_value] at hv
        rwa [signed]

end K256.Proofs.Verify.Core.Scalars.Inverse
