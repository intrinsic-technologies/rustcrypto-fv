import AesGcm.Proofs.AES16.KeySchedule.Generation.State
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem start_reaches (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hsp : args[4].get 64 = sp) (hTypes : GPRsTyped args)
    (hDF : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hbuffer : args[14].get 64 = base use256 sp)
    (hindex : args[15].get 64 = (if use256 then 8 else 0)) :
    ∃ nextArgs : Values Value Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l105856 else .l1043d2), args, mem⟩, []⟩
        ⟨⟨label use256 ((variant use256).Nk / 4), nextArgs, mem⟩, []⟩ ∧
      Ready use256 ((variant use256).Nk / 4) sp nextArgs ∧ SameFP args nextArgs := by
  cases use256 with
  | false =>
    refine ⟨?next0, .single ?exec0, ?ready0, ?fp0⟩
    case exec0 =>
      change (LIR.program.runBlock (dialect code) ⟨.l1043d2, args, mem⟩).next
        (dialect code) [] = .next _
      cfg_eval [LIR.program]
      rfl
    case ready0 =>
      refine ⟨hsp, ?_, hDF, h39, h50, h51, hbuffer, hindex, ?_⟩
      · runtime_typed
      · change (0 : BitVec 64) = 0 ∧ (16 : BitVec 64) = 16 ∧
          args[14].get 64 = base false sp + 0
        exact ⟨rfl, rfl, (BitVec.add_zero _).symm ▸ hbuffer⟩
    case fp0 => exact ⟨rfl, rfl, rfl⟩
  | true =>
    refine ⟨?next1, .single ?exec1, ?ready1, ?fp1⟩
    case exec1 =>
      change (LIR.program.runBlock (dialect code) ⟨.l105856, args, mem⟩).next
        (dialect code) [] = .next _
      cfg_eval [LIR.program]
      rfl
    case ready1 =>
      refine ⟨hsp, ?_, hDF, h39, h50, h51, hbuffer, hindex, ?_⟩
      · runtime_typed
      · exact ⟨rfl, rfl, rfl⟩
    case fp1 => exact ⟨rfl, rfl, rfl⟩

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
