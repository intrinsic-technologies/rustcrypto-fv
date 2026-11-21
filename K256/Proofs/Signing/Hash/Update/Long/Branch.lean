import K256.Proofs.Verify.Hash.Update.Lengths
import K256.Proofs.Signing.Hash.Update.Slice

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

theorem toCompression {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64} {n : Nat}
    (args : Slice sp src n a) (branch : 64 ≤ n) (low : n < 2^64) :
    ∃ b, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l105509,a,m⟩, []⟩ ⟨⟨.l10555a,b,m⟩, []⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,4,12,14,15,22,39,50,51] → b[i] = a[i]) ∧
      b[2] = ⟨64, BitVec.ofNat 64 (n / 64)⟩ ∧ b[6] = ⟨64,src⟩ ∧
      b[13] = ⟨64, BitVec.ofNat 64 n⟩ := by
  have first : ∃ c : Values Value Reg.count, program.runBlock (dialect Extracted.programImage)
      ⟨.l105509,a,m⟩ = .jump ⟨.l1055b1,c,m⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,6,12,14,15,22,39,50,51] → c[i] = a[i] := by
    refine ⟨?_, ?run, ?keep⟩
    case run =>
      have z : a[12].get 64 = 0 := congrArg (Value.get 64) args.buffered
      cfg_eval [z]
      rfl
    case keep =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨c, step, keep⟩ := first
  have hsize : c[5].get 64 = BitVec.ofNat 64 n :=
    congrArg (Value.get 64) ((keep 5 (by decide)).trans args.size)
  have count : BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
    rw [Verify.Hash.Update.block_count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt low]
  have positive : BitVec.ofNat 64 (n / 64) ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    change (n / 64) % 2^64 = 0 at this
    omega
  have second : ∃ b : Values Value Reg.count, program.runBlock (dialect Extracted.programImage)
      ⟨.l1055b1,c,m⟩ = .jump ⟨.l10555a,b,m⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,4,6,12,14,15,22,39,50,51] → b[i] = c[i]) ∧
      b[2] = ⟨64, BitVec.ofNat 64 (n / 64)⟩ ∧ b[13] = ⟨64, BitVec.ofNat 64 n⟩ := by
    refine ⟨?_, ?run, ?keep, ?blocks, ?length⟩
    case run =>
      have nz : (BitVec.ofNat 64 (n / 64) == 0) = false := beq_eq_false_iff_ne.mpr positive
      cfg_eval [hsize, count, nz]
      rfl
    case keep =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case blocks => rfl
    case length => rfl
  obtain ⟨b, next, kept, blocks, len⟩ := second
  refine ⟨b, .step (congrArg (Transfer.next _ []) step) (.step (congrArg (Transfer.next _ []) next) (.refl _)),
    ?_, blocks, (kept 6 (by decide)).trans ((keep 6 (by decide)).trans args.source), len⟩
  intro i hi
  apply (kept i ?_).trans (keep i ?_) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢ <;> omega

end Update
end K256.Proofs.Signing.Hash
