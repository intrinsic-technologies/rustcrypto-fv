import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Lift.Eval
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Sec1.Parser.Frame

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Sec1.LIR

theorem failBlock {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} :
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l106560, args, mem⟩ = .jump ⟨.l106565, next, mem⟩ ∧
      next[0] = ⟨64, 1⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [4, 5, 7, 13, 22, 39, 50, 51] → next[i] = args[i] := by
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval
    rfl
  case post =>
    refine ⟨rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem returnBlock {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {sp dst status ret : BitVec 64}
    (rsp : args[4].get 64 = sp - 344) (rdi : args[7].get 64 = dst) (rax : args[0].get 64 = status)
    (writable : Writable code mem dst 8)
    (included : ∀ x ∈ codeRange 0x106565 bytes_l106565, x ∈ code)
    (slots : Readable mem (sp - 32) 40) (apart : RangeApart dst 8 (sp - 32) 40)
    (returnAddress : memLoad mem sp 64 = ret) (low : ret.toNat < 2 ^ 32) :
    ∃ out : Output Value Ram Reg.count,
      program.runBlock (dialect code) ⟨.l106565, args, mem⟩ = .returned out ∧
      out.store = memStore mem dst status ∧ out.tag = some ⟨64, ret⟩ ∧
      out.values[0] = ⟨64, dst⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      out.values[3] = ⟨64, memLoad mem (sp - 32) 64⟩ ∧
      out.values[12] = ⟨64, memLoad mem (sp - 24) 64⟩ ∧
      out.values[14] = ⟨64, memLoad mem (sp - 16) 64⟩ ∧
      out.values[15] = ⟨64, memLoad mem (sp - 8) 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5, 13, 22, 39, 50, 51] → out.values[i] = args[i] := by
  let stored := memStore mem dst status
  have hw : StoreOk code mem dst 8 0x106565 3 :=
    ParseSignature.storeOk_of_codeRange (off := 0) writable included (by decide)
  have stack : sp - 344 + 312 = sp - 32 := by bv_omega
  have step₁ : sp - 32 + 8 = sp - 24 := by bv_omega
  have step₂ : sp - 24 + 8 = sp - 16 := by bv_omega
  have step₃ : sp - 16 + 8 = sp - 8 := by bv_omega
  have read (off : BitVec 64) (inside : (32 - off).toNat + 8 ≤ 40) : LoadOk stored (sp - off) 8 :=
    LoadOk.of_offsets (slots.memStore dst status) (addr_sub sp off) (addr_sub sp 32)
      (by rwa [show 0 - off - (0 - 32) = 32 - off by bv_omega])
  have h₁ := read 32 (by decide)
  have h₂ := read 24 (by decide)
  have h₃ := read 16 (by decide)
  have h₄ := read 8 (by decide)
  have h₅ : LoadOk stored sp 8 :=
    LoadOk.of_offsets (slots.memStore dst status) (addr_self sp) (addr_sub sp 32) (by decide)
  have value (off : BitVec 64) (inside : (32 - off).toNat + 8 ≤ 40) :
      memLoad stored (sp - off) 64 = memLoad mem (sp - off) 64 := by
    apply memLoad_memStore_of_rangeApart
    have address : sp - 32 + BitVec.ofNat 64 (32 - off).toNat = sp - off := by
      simp only [BitVec.ofNat_toNat]
      bv_omega
    rw [← address]
    exact RangeApart.right_sub apart inside
  have v₅ : memLoad stored sp 64 = ret := by
    rw [← returnAddress]
    apply memLoad_memStore_of_rangeApart
    have a := RangeApart.right_sub apart (off := 32) (m' := 8) (by decide)
    change RangeApart dst 8 (sp - 32 + 32) 8 at a
    rwa [BitVec.sub_add_cancel] at a
  dsimp only [stored] at h₁ h₂ h₃ h₄ h₅ v₅
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval [rsp, rdi, rax, hw, stack, step₁, step₂, step₃, BitVec.sub_add_cancel, h₁, h₂, h₃, h₄,
      h₅, v₅, low]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (Value.mk 64) (value 32 (by decide))
    · exact congrArg (Value.mk 64) (value 24 (by decide))
    · exact congrArg (Value.mk 64) (value 16 (by decide))
    · exact congrArg (Value.mk 64) (value 8 (by decide))
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Parser.Frame
