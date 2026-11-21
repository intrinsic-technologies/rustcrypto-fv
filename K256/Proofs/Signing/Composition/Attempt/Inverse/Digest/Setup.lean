import K256.Proofs.Verify.Choice
import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.State

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Verify.LIR
open Generate.Generator.Multiply (scalarWords)
open Standards.NIST.SHA2

def setupRegions (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-8).toNat,296⟩,⟨(p+624).toNat,32⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem setupDigestFill {p : BitVec 64} {a : Registers} {m : Ram} {k : Nat}
    (area : Writable Extracted.programImage m (p-8) 664)
    (depth : 216 ≤ p.toNat) (rsp : a[4] = ⟨64,p⟩) (dst : a[13] = ⟨64,p+256⟩)
    (nonce : WordsAt m (p+128) 64 (scalarWords k)) :
    ∃ (b : Registers) (n : Ram),
      Verify.LIR.program.runBlock (dialect Extracted.programImage) ⟨.l1059fb,a,m⟩ =
        .call ⟨.l127d70,b,n⟩ (Verify.resumeAt .l105aaa 0x105aaa) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[6] = ⟨64,32⟩ ∧ b[7] = ⟨64,p+352⟩ ∧
      b[1] = ⟨64,4⟩ ∧ b[2] = ⟨64,p+256⟩ ∧ b[8] = ⟨64,256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n (setupRegions p) ∧ memLoad n (p-8) 64 = 0x105aaa ∧
      WordsAt n (p+624) 64 (scalarWords k) := by
  have sp := congrArg (Value.get 64) rsp
  have target := congrArg (Value.get 64) dst
  simp only [Value.get_mk_setWidth, BitVec.setWidth_eq] at sp target
  have room : 8 ≤ p.toNat := Nat.le_trans (by decide) depth
  have low := area.readable.low
  refine ⟨?_,?_,?run,?post⟩
  case run =>
    cfg_eval [sp, target]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1059fb)
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
    · rintro ⟨i,_⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · unfold setupRegions
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · intro i hi
      have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      have input := nonce i hi
      rcases indices with rfl|rfl|rfl|rfl <;>
        simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,Lift.reduceAddOffset] at input ⊢
      all_goals segment_words [input]

end K256.Proofs.Signing.Composition.Attempt.Inverse
