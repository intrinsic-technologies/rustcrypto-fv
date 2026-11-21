import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.Hash.Compression.Return

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {entry : CFG.Values Value Reg.count} {original : Ram} {sp dst src : BitVec 64}
    {initial : Array UInt32} {input : ByteArray}

theorem empty (call : Call entry original sp dst src initial input) (short : input.size / 64 = 0) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1218e0, entry, original⟩, []⟩ out ∧
      Returned entry original sp dst initial out := by
  have rdx : entry[2].get 64 = 0 := by rw [call.rdx, short]; rfl
  have branch : ∃ next : CFG.Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1218e0, entry, original⟩ =
        .jump ⟨.l1240f8, next, original⟩ ∧ next[4] = entry[4] ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        next[i] = entry[i] := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [rdx]
      rfl
    case post =>
      refine ⟨rfl, ?_⟩
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
  obtain ⟨next, branch, rsp, same⟩ := branch
  obtain ⟨out, run, mem, tag, stack, saved⟩ := ret (rsp ▸ call.rsp) call.returnReadable call.returnLow
  refine ⟨out, .next (congrArg (Transfer.next _ []) branch) (.done (congrArg (Transfer.next _ []) run)),
    ⟨mem ▸ call.state, mem ▸ .refl _ _, tag, stack, fun i hi => (saved i hi).trans (same i hi)⟩⟩

end K256.Proofs.Verify.Hash.Compression
