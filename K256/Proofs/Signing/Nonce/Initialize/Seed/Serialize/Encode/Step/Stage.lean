import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.State
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize.Encode
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR Verify.Core

theorem stageWord {a : Registers} {m : Ram} {sp dst src v : BitVec 64} {k : Nat}
    (hk : k < 4) (rsp : a[4].get 64 = sp - 72) (r13 : a[13].get 64 = src)
    (r14 : a[14].get 64 = dst) (index : a[5].get 64 = BitVec.ofNat 64 k)
    (rest : a[2].get 64 = BitVec.ofNat 64 (32-8*k))
    (cursor : a[3].get 64 = BitVec.ofNat 64 (32-8*k)) (zero : a[12].get 64 = 0)
    (read : LoadOk m (wordAddr src 64 k) 8) (word : memLoad m (wordAddr src 64 k) 64 = v)
    (store : StoreOk Extracted.programImage m (sp-56) 8 0x100132 5)
    (push : StoreOk Extracted.programImage (memStore m (sp-56) (bswapSpec v)) (sp-80) 8 0x100145 6)
    (slot : LoadOk (memStore m (sp-56) (bswapSpec v)) 0x203dd0 8)
    (target : memLoad (memStore m (sp-56) (bswapSpec v)) 0x203dd0 64 = 0x12a820) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l100110,a,m⟩ =
      .call ⟨.l12a820,b,memStore (memStore m (sp-56) (bswapSpec v)) (sp-80) (0x10014b : BitVec 64)⟩
        ⟨.l10014b,#v[],rfl,some ⟨64,0x10014b⟩⟩ ∧
      b[7].get 64 = wordAddr dst 64 (3-k) ∧ b[6].get 64 = sp-56 ∧ b[2].get 64 = 8 ∧
      b[4] = ⟨64,sp-80⟩ ∧ b[3] = ⟨64,BitVec.ofNat 64 (32-8*(k+1))⟩ ∧
      b[5] = ⟨64,BitVec.ofNat 64 (k+1)⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have addr : src + (BitVec.ofNat 64 k <<< 3) = wordAddr src 64 k := by
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have cf : (subSpec (BitVec.ofNat 64 (32-8*k)) 8).2.CF = false := by
    rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel
  have diff : BitVec.ofNat 64 (32-8*k) - (BitVec.ofNat 64 (32-8*k)-8) = 8 := by bv_omega
  have next : BitVec.ofNat 64 (32-8*k)-8 = BitVec.ofNat 64 (32-8*(k+1)) := by
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have dest : BitVec.ofNat 64 (32-8*(k+1)) + dst = wordAddr dst 64 (3-k) := by
    rw [BitVec.add_comm]
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  rw [next] at diff
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp,r13,r14,index,rest,cursor,zero]
    simp only [addr,read,word,store,target,push,slot,and_self,↓reduceIte,cf,Bool.false_eq_true,
      diff,BitVec.sub_self,
      next,dest]
    rfl
  case post =>
    refine ⟨rfl,?_,rfl,rfl,rfl,?_,?_⟩
    · change (sp - 72 + (if (subSpec (8#64) 8).2.CF = true then 0 else 0)) + 16 = sp - 56
      simp only [ite_self]
      bv_omega
    · rcases cases with rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i,_⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end K256.Proofs.Signing.Nonce.Initialize.Encode
