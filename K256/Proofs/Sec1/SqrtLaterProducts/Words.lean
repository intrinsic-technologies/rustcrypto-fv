import K256.Proofs.Sec1.SqrtLaterProducts.Certificate
import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Value
import K256.Proofs.Sec1.SqrtChainExecution.Bounds

namespace K256.Proofs.Sec1.SqrtLaterProducts

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open Common.Field.Multiply SqrtChainExecution
open LIR (lifted)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem three : WordCertificate 2 := by
  certify_product .l116316 .third 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem four : WordCertificate 3 := by
  certify_product .l1167bf .other 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem five : WordCertificate 4 := by
  certify_product .l116c14 .fifth 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem six : WordCertificate 5 := by
  certify_product .l117297 .other 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem seven : WordCertificate 6 := by
  certify_product .l117bde .other 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem eight : WordCertificate 7 := by
  certify_product .l118081 .other 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem nine : WordCertificate 8 := by
  certify_product .l118511 .other 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem ten : WordCertificate 9 := by
  certify_product .l118991 .other 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem eleven : WordCertificate 10 := by
  certify_product .l118e1a .other 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem twelve : WordCertificate 11 := by
  certify_product .l119780 .other 40

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem thirteen : WordCertificate 12 := by
  certify_product .l119cc0 .other 40

private theorem applyCertificate (i : Fin 13) (cert : WordCertificate i)
    {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    {args : Values Value Reg.count} {mem : Ram}
    (ha : FieldRepr a x 8) (st : ProductState code fr a i.castSucc args mem)
    (hsp : args[4].get 64 = fr.rsp - 440) (hw : Writable code mem (fr.rsp - 440 - 8) 440)
    (hb : 8 ≤ (fr.rsp - 440).toNat) (hl : (fr.rsp - 440).toNat + 432 ≤ 2^32) :
    OutputWords (fr.rsp - 440) (words a (2 * (i.val + 1)))
      (lifted.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩) := by
  have input : WordsAt mem (productInputBase i (fr.rsp - 440)) 64 (words a (2 * i.val + 1)) := by
    unfold productInputBase
    split
    · exact st.copied ‹_›
    · have addr : fr.rsp - (440 : Word) + 40 = fr.rsp - 400 := by
        rw [show (440 : Word) = 400 + 40 by decide +kernel, ← BitVec.sub_sub, BitVec.sub_add_cancel]
      rw [addr]
      exact st.squared
  have result := cert hsp hw hb hl st.saved input
  rw [SqrtSchedule.mulWords_eq _ _ _ (high_product_bound ha _ _)] at result
  have step : words a (2 * (i.val + 1)) =
      Common.Field.mulWords (words a (2 * factorIndex[i])) (words a (2 * i.val + 1)) :=
    (chainWord_step squareWords Common.Field.mulWords a i).1
  exact step.symm ▸ result

theorem productWords (i : Fin 13) (hi : 2 ≤ i.val)
    {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    {args : Values Value Reg.count} {mem : Ram}
    (ha : FieldRepr a x 8) (st : ProductState code fr a i.castSucc args mem)
    (hsp : args[4].get 64 = fr.rsp - 440) (hw : Writable code mem (fr.rsp - 440 - 8) 440)
    (hb : 8 ≤ (fr.rsp - 440).toNat) (hl : (fr.rsp - 440).toNat + 432 ≤ 2^32) :
    OutputWords (fr.rsp - 440) (words a (2 * (i.val + 1)))
      (lifted.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩) := by
  refine applyCertificate i ?_ ha st hsp hw hb hl
  obtain ⟨j, hj⟩ := i
  change 2 ≤ j at hi
  have cases : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact @three
  · exact @four
  · exact @five
  · exact @six
  · exact @seven
  · exact @eight
  · exact @nine
  · exact @ten
  · exact @eleven
  · exact @twelve
  · exact @thirteen

end K256.Proofs.Sec1.SqrtLaterProducts
