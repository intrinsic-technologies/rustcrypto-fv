import K256.Proofs.Generate.Generator.Affine.Invert.Contract
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.LIR.Generated.Values
import K256.Proofs.Sec1.Serialize.Pack
import K256.Proofs.Sec1.Tactic.Lemma.Refine

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC
namespace Invert.PackCall

def packed (u : Limbs) : Vector Word 4 :=
  #v[u[1] <<< 52 ||| u[0], u[2] <<< 40 ||| u[1] >>> 12,
     u[3] <<< 28 ||| u[2] >>> 24, u[4] <<< 16 ||| u[3] >>> 36]

theorem packed_value (u : Limbs) (w : Sec1.Serialize.Normalize.Widths u) :
    Invert.value (packed u) = limbValue u := by
  have h := Sec1.Serialize.packWords_value u w
  change ((bswapSpec (bswapSpec _)).toNat * 2^64 + (bswapSpec (bswapSpec _)).toNat) * 2^128 +
    (bswapSpec (bswapSpec _)).toNat * 2^64 + (bswapSpec (bswapSpec _)).toNat = _ at h
  rw [bswapSpec_bswapSpec, bswapSpec_bswapSpec, bswapSpec_bswapSpec, bswapSpec_bswapSpec] at h
  exact h

def pushed (m : Ram) (q : Word) (w : Vector Word 4) (n : Nat) (hn : n ≤ 4) : Ram :=
  match n with
  | 0 => m
  | n + 1 => memStore (pushed m q w n (by omega)) (if n = 0 then q else wordAddr q 64 n) w[n]

def packedStore (m : Ram) (q : Word) (w : Vector Word 4) : Ram :=
  memStore (pushed m q w 4 (by decide)) (q - 8) (0x10ed84 : Word)

theorem packBlock {code : CodeMap} {a : Registers} {m : Ram} {q : Word} {u : Limbs}
    (rsp : a[4].get 64 = q) (input : WordsAt m (q + 88) 64 u)
    (read : ∀ k : Nat, k < 5 → LoadOk m (wordAddr (q + 88) 64 k) 8)
    (store0 : StoreOk code m q 8 0x10ed4c 4)
    (store1 : StoreOk code (pushed m q (packed u) 1 (by decide)) (q + 8) 8 0x10ed50 5)
    (store2 : StoreOk code (pushed m q (packed u) 2 (by decide)) (q + 16) 8 0x10ed55 5)
    (store3 : StoreOk code (pushed m q (packed u) 3 (by decide)) (q + 24) 8 0x10ed5a 5)
    (push : StoreOk code (pushed m q (packed u) 4 (by decide)) (q - 8) 8 0x10ed7f 5) :
    ∃ b : Registers,
      program.runBlock (dialect code) ⟨.l10ed05, a, m⟩ =
        .call ⟨.l108e30, b, packedStore m q (packed u)⟩ (callFrame .l10ed84 0x10ed84) ∧
      b[4] = ⟨64, q - 8⟩ ∧ b[1] = ⟨64, 0x27c7f6e22ddacacf⟩ ∧
      b[2] = ⟨64, 0x2021e0⟩ ∧ b[6] = ⟨64, q⟩ ∧ b[7] = ⟨64, q + 88⟩ ∧
      b[8] = ⟨64, 0x202180⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have rd0 : LoadOk m (q + 88) 8 := by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using read 0 (by decide)
  have rd1 : LoadOk m (q + 96) 8 := by
    rw [← show wordAddr (q + 88) 64 1 = q + 96 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact read 1 (by decide)
  have rd2 : LoadOk m (q + 104) 8 := by
    rw [← show wordAddr (q + 88) 64 2 = q + 104 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact read 2 (by decide)
  have rd3 : LoadOk m (q + 112) 8 := by
    rw [← show wordAddr (q + 88) 64 3 = q + 112 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact read 3 (by decide)
  have rd4 : LoadOk m (q + 120) 8 := by
    rw [← show wordAddr (q + 88) 64 4 = q + 120 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact read 4 (by decide)
  have u0 : memLoad m (q + 88) 64 = u[0] := by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using input 0 (by decide)
  have u1 : memLoad m (q + 96) 64 = u[1] := by
    rw [← show wordAddr (q + 88) 64 1 = q + 96 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact input 1 (by decide)
  have u2 : memLoad m (q + 104) 64 = u[2] := by
    rw [← show wordAddr (q + 88) 64 2 = q + 104 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact input 2 (by decide)
  have u3 : memLoad m (q + 112) 64 = u[3] := by
    rw [← show wordAddr (q + 88) 64 3 = q + 112 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact input 3 (by decide)
  have u4 : memLoad m (q + 120) 64 = u[4] := by
    rw [← show wordAddr (q + 88) 64 4 = q + 120 by simp only [wordAddr, BitVec.add_assoc]; rfl]
    exact input 4 (by decide)
  refine ⟨?_, ?block, ?regs⟩
  case block =>
    cfg_eval [b_l10ed05_1, rsp]
    simp only [rd0, rd1, rd2, rd3, rd4, u0, u1, u2, u3, u4, ↓reduceIte]
    refine (ite_eq_left store0).trans ?_
    refine (ite_eq_left store1).trans ?_
    refine (ite_eq_left store2).trans ?_
    refine (ite_eq_left store3).trans ?_
    refine (ite_eq_left push).trans ?_
    rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Invert.PackCall

end K256.Proofs.Generate.Generator.Affine
