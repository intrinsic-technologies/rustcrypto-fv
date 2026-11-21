import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem ret {args : CFG.Values Value Reg.count} {mem : Ram} {sp : BitVec 64}
    (rsp : args[4].get 64 = sp) (read : Readable mem sp 8)
    (low : (memLoad mem sp 64).toNat < 2^32) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l1240f8, args, mem⟩ =
        .returned out ∧ out.store = mem ∧ out.tag = some ⟨64, memLoad mem sp 64⟩ ∧
      out.values[4] = ⟨64, sp + 8⟩ ∧ ∀ i : Fin Reg.count,
        i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → out.values[i] = args[i] := by
  have ok : LoadOk mem sp 8 ∧ (memLoad mem sp 64).toNat < 2^32 :=
    ⟨⟨read.low, read.present⟩, low⟩
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp, ok]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl

end K256.Proofs.Verify.Hash.Compression
