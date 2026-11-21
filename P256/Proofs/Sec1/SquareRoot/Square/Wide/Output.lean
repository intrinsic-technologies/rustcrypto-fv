import P256.Proofs.Sec1.SquareRoot.Square.Wide.BodyInterface
import P256.Proofs.Field.Schoolbook.Bytes

set_option autoImplicit false

open P256.Proofs.Field.Schoolbook (packEight)
open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Field.Schoolbook (bytes_of_memLoad_packEight limbsOfNat)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem sourceWords_nat {s : RamState} {x : Nat}
    (hx : Nat256At s (s.regValue .rsi) x) :
    (sourceWords s).map BitVec.toNat = limbsOfNat x := by
  ext i hi
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp only [Vector.getElem_map]
  · change (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (8*0)) 64).toNat = (limbsOfNat x)[0]
    rw [hx.memLoad_limb 0 (by decide)]
    simp [limbsOfNat, wordBase]
  · change (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (8*1)) 64).toNat = (limbsOfNat x)[1]
    rw [hx.memLoad_limb 1 (by decide)]
    simp [limbsOfNat, wordBase]
  · change (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (8*2)) 64).toNat = (limbsOfNat x)[2]
    rw [hx.memLoad_limb 2 (by decide)]
    simp [limbsOfNat, wordBase]
  · change (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (8*3)) 64).toNat = (limbsOfNat x)[3]
    rw [hx.memLoad_limb 3 (by decide)]
    simp [limbsOfNat, wordBase]

theorem body_output_words {s t : RamState} (h : (bodyEffect s).Holds s t)
    (j : Nat) (hj : j < 8) :
    memLoad t.external (s.regValue .rdi+BitVec.ofNat 64 (8*j)) 64 =
      (squareWords (sourceWords s))[j] := by
  have hs : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  have hw := h.writes
  simp only [bodyEffect, Write.AllHold] at hw
  rcases hw with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, h5, h6, h7⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem body_output_bytes {s t : RamState} (h : (bodyEffect s).Holds s t)
    (allocated : ∀ i < 64, (t.external[s.regValue .rdi+BitVec.ofNat 64 i]?).isSome) :
    Bytes t.external (s.regValue .rdi) 64
      (fun i => UInt8.ofNat (packEight ((squareWords (sourceWords s)).map BitVec.toNat) / 256^i % 256)) := by
  refine bytes_of_memLoad_packEight _ ?_ allocated ?_
  · intro i
    simpa using (squareWords (sourceWords s))[i].isLt
  · intro j hj
    simpa only [Vector.getElem_map, BitVec.ofNat_toNat, BitVec.setWidth_eq] using body_output_words h j hj

end P256.Proofs.Sec1.SquareRoot.Square.Wide
