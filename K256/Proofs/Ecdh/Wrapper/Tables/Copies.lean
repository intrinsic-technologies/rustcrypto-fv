import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Caller.SecondCopy

namespace K256.Proofs.Ecdh.Wrapper.Tables

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Generate.Generator.Multiply.Caller

theorem copyRightCall {a : Arguments} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820)
    (src : a[15].get 64 = sp + 3224) (push : StoreOk Extracted.programImage m (sp - 8) 8 0x101a4c 3) :
    ∃ b : Arguments, program.runBlock (dialect Extracted.programImage) ⟨.l101a3c, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x101a4f : BitVec 64)⟩ (callFrame .l101a4f 0x101a4f) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 1304 ∧ b[6].get 64 = sp + 3224 ∧
      b[2].get 64 = 960 ∧ ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → b[i] = a[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l101a3c, rsp, target, src, push]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem copyTableCall {a : Arguments} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820)
    (src : a[12].get 64 = sp + 344) (push : StoreOk Extracted.programImage m (sp - 8) 8 0x101a62 3) :
    ∃ b : Arguments, program.runBlock (dialect Extracted.programImage) ⟨.l101a4f, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x101a65 : BitVec 64)⟩ (callFrame .l101a65 0x101a65) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 4184 ∧ b[6].get 64 = sp + 344 ∧
      b[2].get 64 = 1920 ∧ b[15] = ⟨64, sp + 4184⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → i.val ≠ 15 → b[i] = a[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l101a4f, rsp, target, src, push]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h ne
    simp only [memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | contradiction

end K256.Proofs.Ecdh.Wrapper.Tables
