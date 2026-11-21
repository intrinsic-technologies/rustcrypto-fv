import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.State

import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def compressRet (second : Bool) : BitVec 64 := if second then 0x1044a4 else 0x104080

def compressResume (second : Bool) : StackFrame Value Label signature Reg.count :=
  ⟨if second then .l1044a4 else .l104080, #v[], rfl, some ⟨64, compressRet second⟩⟩

def compressMemory (m : Ram) (s ret : BitVec 64) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore m
    (s + 416) (0x5be0cd191f83d9ab : BitVec 64))
    (s + 408) (0x9b05688c510e527f : BitVec 64))
    (s + 400) (0xa54ff53a3c6ef372 : BitVec 64))
    (s + 392) (0xbb67ae856a09e667 : BitVec 64))
    (s + 391) (0 : BitVec 8)) (s + 424) (1 : BitVec 64)) (s - 8) ret

theorem compressCallBlock {a : Verify.Core.Registers} {m : Ram} (fr : Activation) (second : Bool)
    (rsp : a[4].get 64 = sp fr) (stack : Writable Extracted.programImage m (sp fr - 8) 440) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage)
      ⟨exitLabel second false,a,m⟩ = .call ⟨.l1218e0,b,compressMemory m (sp fr) (compressRet second)⟩
        (compressResume second) ∧ b[4].get 64 = sp fr - 8 ∧ b[7].get 64 = sp fr + 392 ∧
      b[6].get 64 = pad fr second ∧ b[2].get 64 = 1 ∧
      b[13] = (if second then ⟨64,sp fr + 392⟩ else a[13]) ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,14,15,22,39,50,51] → b[i] = a[i] := by
  cases second
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · first
      | change program.runBlock _ ⟨.l10400a, a, m⟩ = _
      | change program.runBlock _ ⟨.l10442e, a, m⟩ = _
      cfg_eval [rsp]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l10400a | slot_guard using code_l10442e)
      rfl
    · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
      rintro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem compressResumeBlock {a : Verify.Core.Registers} {m : Ram} (s : BitVec 64) (second : Bool)
    (rsp : a[4].get 64 = s) (stack : Writable Extracted.programImage m (s + 391) 1) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage)
      ⟨(compressResume second).target,a,m⟩ =
      .jump ⟨head second true,b,memStore m (s + 391) (0 : BitVec 8)⟩ ∧ b[0] = ⟨64,3⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  cases second
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · first
      | change program.runBlock _ ⟨.l104080, a, m⟩ = _
      | change program.runBlock _ ⟨.l1044a4, a, m⟩ = _
      cfg_eval [rsp]
      refine Eq.trans (ite_eq_left ?_) ?_
      · first | slot_guard using code_l104080 | slot_guard using code_l1044a4
      · rfl
    · refine ⟨rfl, ?_⟩
      rintro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
