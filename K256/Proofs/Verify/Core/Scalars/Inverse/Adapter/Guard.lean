import K256.Proofs.Verify.Core.Scalars.Digest.Prepare
import K256.Proofs.Verify.Core.Memory

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Adapter

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem passGuard (b : Registers) (m : Ram) (sp : BitVec 64)
    (rsp : b[4].get 64 = sp) (win : Writable Extracted.programImage m sp 137)
    (flag : memLoad m (sp+40) 8 = 1) :
    ∃ c, Reaches .l10519d b m .l1051b1 c (memStore m (sp+136) (1 : BitVec 8)) ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → c[i] = b[i] := by
  have rd : LoadOk m (sp+40) 1 := by slot_guard using code_l10519d
  have wr : StoreOk Extracted.programImage m (sp+136) 1 0x1051a2 7 := by slot_guard using code_l10519d
  refine ⟨?c, .single ?step, ?regs⟩
  case step =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [rsp,flag]
    simp only [rd,wr,ite_true]
    rfl
  case regs =>
    rintro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Scalars.Inverse.Adapter
