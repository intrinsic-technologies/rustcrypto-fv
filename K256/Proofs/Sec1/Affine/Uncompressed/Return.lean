import K256.Proofs.Sec1.Affine.Uncompressed.Entry

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

theorem finalChoice (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : Word) (rsp : args[4].get 64 = sp) (read : LoadOk mem (sp + 200) 8)
    (push : StoreOk code mem (sp - 8) 8 0x12032b 5) :
    ∃ regs, program.runBlock (dialect code) ⟨.l12031e, args, mem⟩ =
        .call ⟨.l127d50, regs, memStore mem (sp - 8) (0x120330 : Word)⟩
          (choiceResume .l120330 0x120330 rfl) ∧
      regs[4].get 64 = sp - 8 ∧
      regs[7].get 64 = (((memLoad mem (sp + 200) 64).setWidth 8) &&&
        (args[0].get 64).setWidth 8).setWidth 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → regs[i] = args[i] := by
  refine ⟨?regs, ?eval, ?post⟩
  case eval => cfg_eval [rsp, read, push]; rfl
  case post =>
    refine ⟨rfl, ?_, ?_⟩
    · change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
      rw [setWidth_mergeGPR8]
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem returnPoint (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : Word) (rsp : args[4].get 64 = sp) (rbx : args[3].get 64 = dst)
    (flag : BitVec 8) (rax : (args[0].get 64).setWidth 8 = flag)
    (guard : StoreOk code mem (dst + 88) 1 0x120330 3)
    (stack : Readable mem (sp + 216) 56)
    (target : (memLoad (memStore mem (dst + 88) flag) (sp + 264) 64).toNat < 2^32) :
    let m := memStore mem (dst + 88) flag
    ∃ out, program.runBlock (dialect code) ⟨.l120330, args, mem⟩ = .returned out ∧
      out.store = m ∧ out.tag = some ⟨64, memLoad m (sp + 264) 64⟩ ∧
      out.values[0] = ⟨64, dst⟩ ∧ out.values[4] = ⟨64, sp + 272⟩ ∧
      out.values[3] = ⟨64, memLoad m (sp + 216) 64⟩ ∧
      out.values[12] = ⟨64, memLoad m (sp + 224) 64⟩ ∧
      out.values[13] = ⟨64, memLoad m (sp + 232) 64⟩ ∧
      out.values[14] = ⟨64, memLoad m (sp + 240) 64⟩ ∧
      out.values[15] = ⟨64, memLoad m (sp + 248) 64⟩ ∧
      out.values[5] = ⟨64, memLoad m (sp + 256) 64⟩ ∧
      out.values[22] = args[22] ∧ out.values[39] = args[39] ∧
      out.values[50] = args[50] ∧ out.values[51] = args[51] := by
  have reads (off : Word) (h : (off - 216).toNat + 8 ≤ 56) :
      LoadOk (memStore mem (dst + 88) flag) (sp + off) 8 :=
    LoadOk.of_offsets (stack.memStore _ flag) rfl rfl h
  dsimp only
  refine ⟨?out, ?eval, ?post⟩
  case eval =>
    cfg_eval [rsp, rbx, rax, guard, target]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; exact reads _ (by decide))
    rfl
  case post => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end K256.Proofs.Sec1.Affine.Uncompressed
