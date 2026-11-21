import P256.Proofs.Field.Schoolbook.Preconditions

set_option autoImplicit false

open P256.Proofs.Program (inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
  {ctx : ExecutionContext s boundary entry}

theorem upper_body (state : BodyState ctx t) (rip : t.RIP = 0x11ca70)
    (source : t.regValue .rsi = s.regValue .rsi) :
    ∃ p l m u, BodyState ctx u ∧ (upperProductsEffect t).Holds t p ∧
      (upperSumsLowEffect p).Holds p l ∧ (upperSumsMiddleEffect l).Holds l m ∧
      (upperSumsHighEffect m).Holds m u ∧ u.RIP = 0x11cb43 := by
  obtain ⟨p, ps, hp⟩ := state.advance (upper_products_correct boundary ctx.pre.outerBoundary)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1ca70 _
      (by decide) upperProductsBytes_extracted)
    (upper_products_pre state rip source) (fun _ h => upper_products_scratch h)
  have pl : ScratchPre 0x11cace 32 p := ps.scratchPre hp.rip (by
    intro j hj
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1cace)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1cace+j) (by omega))
  obtain ⟨l, ls, hl⟩ := ps.advance (upper_sums_low boundary ctx.pre.outerBoundary)
    (programText_slice (programLoaded_codeIn ps.loaded) 0x1cace _
      (by decide) upperSumsLowBytes_extracted) pl (fun _ h => upper_low_scratch h)
  have pm : ScratchPre 0x11caee 44 l := ls.scratchPre hl.rip (by
    intro j hj
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1caee)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1caee+j) (by omega))
  obtain ⟨m, ms, hm⟩ := ls.advance (upper_sums_middle boundary ctx.pre.outerBoundary)
    (programText_slice (programLoaded_codeIn ls.loaded) 0x1caee _
      (by decide) upperSumsMiddleBytes_extracted) pm (fun _ h => upper_middle_scratch h)
  have pu : ScratchPre 0x11cb1a 41 m := ms.scratchPre hm.rip (by
    intro j hj
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1cb1a)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1cb1a+j) (by omega))
  obtain ⟨u, us, hu⟩ := ms.advance (upper_sums_high boundary ctx.pre.outerBoundary)
    (programText_slice (programLoaded_codeIn ms.loaded) 0x1cb1a _
      (by decide) upperSumsHighBytes_extracted) pu (fun _ h => upper_high_scratch h)
  exact ⟨p, l, m, u, us, hp, hl, hm, hu, hu.rip⟩

end P256.Proofs.Field.Schoolbook
