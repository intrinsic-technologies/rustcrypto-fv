import K256.Proofs.Common.Invert.Correct
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.Generator.Affine.Invert.Parameters

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

private theorem writable_modulus_apart {m : Ram} {a : Word} {n : Nat}
    (w : Writable Extracted.programImage m a n) (hn : 0 < n) :
    a.toNat + n ≤ 0x2021e0 ∨ 0x202200 ≤ a.toNat := by
  apply Classical.byContradiction
  intro neither
  let p := max a.toNat 0x2021e0
  let i := p - 0x200000
  have hi : i < Extracted.rodataBytes.toList.length := by
    rw [chunked_toList_length, Common.rodataBytes_size]
    dsimp only [i, p]
    omega
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  let entry := (Extracted.rodataAddress + BitVec.ofNat 64 i, Extracted.rodataBytes.toList[i])
  have inCode : entry ∈ Extracted.programImage :=
    List.mem_flatMap.mpr ⟨sec, .tail _ (.head _), mem_codeRange _ _ _ hi⟩
  apply w.notCode entry inCode (p - a.toNat) (by dsimp only [p]; omega)
  change (0x200000 : Word) + BitVec.ofNat 64 (p - 0x200000) = _
  rw [← ofNat_toNat_add, ← ofNat_toNat_add a]
  apply congrArg (BitVec.ofNat 64)
  change 0x200000 + (p - 0x200000) = a.toNat + (p - a.toNat)
  dsimp only [p]
  omega

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
    (ptr : a[1].get 64 = 0x2021e0)
    (flag : (a[2].get 8 &&& 1) = (if neg then 1 else 0)) (bound : x.natAbs < modulus) :
    ∃ out, CalleeExec .l109c00 a m out ∧ CalleeResult a m sp dst ret 56 32 out ∧
      ∃ v : Vector Word 4, WordsAt out.store dst 64 v ∧
        value v = ((if neg then -x else x) % (modulus : Int)).toNat := by
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
  have modApart := writable_modulus_apart stack (by decide)
  have r0 := (modulus_loaded fr.image 0).1
  have r1 := (modulus_loaded fr.image 1).1
  have r2 := (modulus_loaded fr.image 2).1
  have r3 := (modulus_loaded fr.image 3).1
  change Readable m 0x2021e0 8 at r0
  change Readable m 0x2021e8 8 at r1
  change Readable m 0x2021f0 8 at r2
  change Readable m 0x2021f8 8 at r3
  have w0 : memLoad m source 64 = v[0] := by
    simpa [wordAddr] using words 0 (by decide)
  have w1 : memLoad m (source + 8) 64 = v[1] := words 1 (by decide)
  have w2 : memLoad m (source + 16) 64 = v[2] := words 2 (by decide)
  have w3 : memLoad m (source + 24) 64 = v[3] := words 3 (by decide)
  have q0 : memLoad m 0x2021e0 64 = modulusWords[0] := (modulus_loaded fr.image 0).2
  have q1 : memLoad m 0x2021e8 64 = modulusWords[1] := (modulus_loaded fr.image 1).2
  have q2 : memLoad m 0x2021f0 64 = modulusWords[2] := (modulus_loaded fr.image 2).2
  have q3 : memLoad m 0x2021f8 64 = modulusWords[3] := (modulus_loaded fr.image 3).2
  have finishRun {o : Output Value Ram Reg.count}
      (run : program.runBlock (dialect Extracted.programImage) ⟨.l109c00, a, m⟩ = .returned o) :
      CalleeExec .l109c00 a m o := by
    apply Program.Exec.done
    simp only [Program.step, run, Transfer.next]
  refine ⟨?out, finishRun ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l109c00
      [rsp, rdi, ptr, hsource, retAddr, w0, w1, w2, w3, q0, q1, q2, q3, sign]
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
      let result := Common.Invert.Correct.correctedWords modulusWords v (a[2].get 8) signByte
      refine ⟨result, ?_, ?_⟩
      · dsimp only
        lifted_word_reads []
        all_goals rw [correctionMask]
        all_goals first | rfl | lifted_word_eq [Common.Invert.Correct.correctedWords]
      · have mag : x.natAbs = value v := by rw [signed]; cases inputNeg <;> simp
        have hb : value v < value modulusWords := by rwa [modulus_value, ← mag]
        have hv := Common.Invert.Correct.correctedWords_value modulusWords v (a[2].get 8) inputNeg neg flag hb
        dsimp only at hv
        rw [modulus_value] at hv
        rwa [signed]

end K256.Proofs.Generate.Generator.Affine.Invert.Core
