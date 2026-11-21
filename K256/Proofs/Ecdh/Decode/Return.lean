import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Sec1.Parser.Result.Blocks
import K256.Proofs.Sec1.Serialize.Choice

namespace K256.Proofs.Ecdh.Decode

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Ecdh.LIR

variable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}

def choiceReturn : StackFrame Value Label signature Reg.count :=
  {target := .l121196, kept := #v[], arity := rfl, guard := some ⟨64, 0x121196⟩}

theorem copyCall {sp dst : BitVec 64}
    (widths : ∀ i : Fin Reg.count, i.val ∈ [2,8,9] → args[i].width = 64)
    (rsp : args[4].get 64 = sp) (rbx : args[3].get 64 = dst)
    (r14 : args[14].get 64 = sp + 144) (r15 : (args[15].get 64).setWidth 8 = 1)
    (read : LoadOk mem (sp + 232) 1) (valid : memLoad mem (sp + 232) 8 = 1)
    (rep : RepMovsOk code mem (args[22].get 1) (sp + 144) dst 11 8 0x12118a 3)
    (push : StoreOk code (memCopy mem dst (sp + 144) 88) (sp - 8) 8 0x121191 5) :
    ∃ next, program.runBlock (dialect code) ⟨.l121177, args, mem⟩ =
      .call ⟨.l127d50, next, memStore (memCopy mem dst (sp + 144) 88) (sp - 8) (0x121196 : BitVec 64)⟩
        choiceReturn ∧ ParseSignature.ArgumentWidths next ∧ next[7].get 64 = 1 ∧ next[4] = ⟨64, sp - 8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,22,39,50,51] → next[i] = args[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, rbx, r14, read, valid, rep, push, r15]
    rfl
  case post =>
    refine ⟨?_, ?_, rfl, ?_⟩
    · rintro ⟨i,hi⟩ h
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact widths 2 (by decide) | exact widths 8 (by decide) | exact widths 9 (by decide)
    · change ((mergeGPR 8 _ _).setWidth 8).setWidth 64 = _
      rw [setWidth_mergeGPR8]
      rfl
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem returnBlock {sp dst : BitVec 64}
    (rsp : args[4].get 64 = sp) (rbx : args[3].get 64 = dst)
    (rax : (args[0].get 64).setWidth 8 = 1)
    (write : StoreOk code mem (dst + 88) 1 0x121196 3)
    (loads : ∀ k ∈ [240,248,256,264], LoadOk (memStore mem (dst + 88) (1 : BitVec 8))
      (sp + BitVec.ofNat 64 k) 8)
    (low : (memLoad (memStore mem (dst + 88) (1 : BitVec 8)) (sp + 264) 64).toNat < 2^32) :
    let m := memStore mem (dst + 88) (1 : BitVec 8)
    ∃ out, program.runBlock (dialect code) ⟨.l121196, args, mem⟩ = .returned out ∧
      out.store = m ∧ out.tag = some ⟨64, memLoad m (sp + 264) 64⟩ ∧
      out.values[0] = ⟨64, dst⟩ ∧ out.values[4] = ⟨64, sp + 272⟩ ∧
      out.values[3] = ⟨64, memLoad m (sp + 240) 64⟩ ∧
      out.values[14] = ⟨64, memLoad m (sp + 248) 64⟩ ∧
      out.values[15] = ⟨64, memLoad m (sp + 256) 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,5,6,7,8,9,12,13,22,39,50,51] → out.values[i] = args[i] := by
  have a := loads 240 (by decide)
  have b := loads 248 (by decide)
  have c := loads 256 (by decide)
  have d := loads 264 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at a b c d
  dsimp only
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, rbx, rax, write, BitVec.add_assoc, low]
    iterate 4
      refine Eq.trans (ite_eq_left ?_) ?_
      first | exact a | exact b | exact c | exact d
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Ecdh.Decode
