import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Sites

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Split.Caller (Site)

set_option maxRecDepth 1600 in
set_option maxHeartbeats 900000 in
theorem callBlock (site : Site) (later : site ≠ .roundFirst)
    {a b : Registers} {m n : Ram} {sp src scalar tables digits : BitVec 64}
    (s : Returned site.prev a m sp src scalar tables digits b n)
    (write : Writable Extracted.programImage n (frameSp sp - 8) 8) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨pc site, b, n⟩ =
      .call ⟨callee site, c, memStore n (frameSp sp - 8) (ret site)⟩
        (callResume (afterPc site) (ret site)) ∧
      ChildRegs site a sp scalar tables c := by
  have rsp : b[4].get 64 = frameSp sp := congrArg (Value.get 64) s.rsp
  have bx := s.tableBase
  have bpReg := s.rbpReg
  have scalarReg := s.scalarReg
  have r13Reg := s.r13Reg
  have r15Reg := s.r15Reg
  have r14Width := s.widths 14 (by decide)
  have control := s.control
  have arguments := s.arguments
  cases site <;> try exact False.elim (later rfl)
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · dsimp only [pc, callee, afterPc, ret]
      cfg_eval [rsp]
      refine Eq.trans (ite_eq_left ?_) ?_
      · first
        | slot_guard using code_l10f188
        | slot_guard using code_l10f1a2
        | slot_guard using code_l10f1b9
        | slot_guard using code_l10f1d3
        | slot_guard using code_l10f1f0
        | slot_guard using code_l10f20a
      · rfl
  all_goals
    dsimp only [Site.prev, bp, r13, r15] at bpReg r13Reg r15Reg
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, bx, ?_, scalarReg, ?_, r14Width, ?_, ?_⟩
  all_goals first
    | rfl
    | exact bpReg
    | exact r13Reg
    | exact r15Reg
    | exact congrArg (fun v => Value.mk 64 (v.get 64)) bpReg
    | exact congrArg (fun v => Value.mk 64 (v.get 64)) r13Reg
    | exact congrArg (fun v => Value.mk 64 (v.get 64)) r15Reg
    | exact congrArg (fun v => Value.mk 64 (v.get 64)) scalarReg
    | (intro h; first | rfl | rcases h with h | h <;> cases h)
    | (rintro ⟨i, hi⟩ h
       simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
       rcases h with rfl | rfl | rfl | rfl | rfl | rfl
       all_goals first
         | rfl
         | exact arguments 1 (by decide)
         | exact arguments 8 (by decide)
         | exact arguments 9 (by decide))
    | (rintro ⟨i, hi⟩ h
       simp only [List.mem_cons, List.not_mem_nil, or_false] at h
       rcases h with rfl | rfl | rfl | rfl
       · exact control 22 (by decide)
       · exact control 39 (by decide)
       · exact control 50 (by decide)
       · exact control 51 (by decide))

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
