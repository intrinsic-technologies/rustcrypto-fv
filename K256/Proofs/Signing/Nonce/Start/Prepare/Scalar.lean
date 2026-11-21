import K256.Proofs.Verify.LIR
import K256.Proofs.Generate.Wrapper.Scalar.Blocks

namespace K256.Proofs.Signing.Nonce.Start

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Generate.Wrapper (writeScalarWords)

theorem serializeScalarBlock {code : CodeMap} {a : Vector Value Reg.count} {mem : Ram}
    {src dst sp retAddr : BitVec 64} {word : Nat → BitVec 64}
    (rsp : a[4].get 64 = sp) (rsi : a[6].get 64 = src) (rdi : a[7].get 64 = dst)
    (load : ∀ i < 4, LoadOk mem (wordAddr src 64 i) 8)
    (words : ∀ i < 4, bswapSpec (memLoad mem (wordAddr src 64 (3 - i)) 64) = word i)
    (store₀ : StoreOk code mem dst 8 0x109e4e 3)
    (store₁ : StoreOk code (writeScalarWords dst word mem 1) (dst + 8) 8 0x109e51 4)
    (store₂ : StoreOk code (writeScalarWords dst word mem 2) (dst + 16) 8 0x109e55 4)
    (store₃ : StoreOk code (writeScalarWords dst word mem 3) (dst + 24) 8 0x109e59 4)
    (retOk : LoadOk (writeScalarWords dst word mem 4) sp 8)
    (ret : memLoad (writeScalarWords dst word mem 4) sp 64 = retAddr)
    (retLow : retAddr.toNat < 2^32) :
    ∃ out, program.runBlock (dialect code) ⟨.l109e30, a, mem⟩ = .returned out ∧
      out.tag = some ⟨64, retAddr⟩ ∧ out.store = writeScalarWords dst word mem 4 ∧
      out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → out.values[i] = a[i]) := by
  have ld₀ : LoadOk mem src 8 := by
    have h := load 0 (by decide)
    rwa [show wordAddr src 64 0 = src from BitVec.add_zero src] at h
  have ld₁ : LoadOk mem (src + 8) 8 := load 1 (by decide)
  have ld₂ : LoadOk mem (src + 16) 8 := load 2 (by decide)
  have ld₃ : LoadOk mem (src + 24) 8 := load 3 (by decide)
  have w₀ : bswapSpec (memLoad mem (src + 24) 64) = word 0 := words 0 (by decide)
  have w₁ : bswapSpec (memLoad mem (src + 16) 64) = word 1 := words 1 (by decide)
  have w₂ : bswapSpec (memLoad mem (src + 8) 64) = word 2 := words 2 (by decide)
  have w₃ : bswapSpec (memLoad mem src 64) = word 3 := by
    have h := words 3 (by decide)
    change bswapSpec (memLoad mem (wordAddr src 64 0) 64) = word 3 at h
    rwa [show wordAddr src 64 0 = src from BitVec.add_zero src] at h
  have zeroAddr : wordAddr dst 64 0 = dst := BitVec.add_zero dst
  have addr₁ : wordAddr dst 64 1 = dst + 8 := rfl
  have addr₂ : wordAddr dst 64 2 = dst + 16 := rfl
  have addr₃ : wordAddr dst 64 3 = dst + 24 := rfl
  simp only [writeScalarWords, zeroAddr, addr₁, addr₂, addr₃] at store₁ store₂ store₃ retOk ret
  refine ⟨?out, ?eval, ?tag, ?memory, ?stack, ?kept⟩
  case eval =>
    cfg_eval
    simp only [rsp, rsi, rdi, ld₀, ld₁, ld₂, ld₃, w₀, w₁, w₂, w₃, store₀,
      store₁, store₂, store₃, retOk, ret, retLow, and_self, ↓reduceIte]
    rfl
  case tag => rfl
  case memory => simp only [writeScalarWords, zeroAddr, addr₁, addr₂, addr₃]
  case stack => rfl
  case kept =>
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.Nonce.Start
