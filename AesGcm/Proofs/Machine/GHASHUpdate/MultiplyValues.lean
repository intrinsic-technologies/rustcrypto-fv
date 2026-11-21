import AesGcm.Proofs.Machine.GHASHInterface
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Guards

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface
open AesGcm.Proofs.Machine.GHASH

theorem multiply_values (code : CodeMap) (hmultiply : MultiplyContract code)
    (mem : Ram) (args : Values Value Reg.count) (sp dst ret low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hdst : args[7].get 64 = dst)
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hdf : args[22] = ⟨1, 0⟩)
    (hread : Readable mem sp 8) (hret : memLoad mem sp 64 = ret)
    (hretlow : ret.toNat < 2^32) (hstack : Writable code mem (sp - 128) 128)
    (hroom : low.toNat + 128 ≤ sp.toNat) (halign : sp.toNat % 16 = 8)
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32)) :
    ∃ o : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨⟨.l102bd0, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, ret⟩ ∧ o.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values ∧
      RamWriteFrame mem o.store [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := polyvalMultiplyWords
          (args[6].get 64 ^^^ memLoad mem (dst + 16) 64)
          (args[2].get 64 ^^^ memLoad mem (dst + 24) 64)
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
       memLoad o.store (dst + 16) 64 = result.1 ∧ memLoad o.store (dst + 24) 64 = result.2) := by
  obtain ⟨o, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code .l102bd0 LIR.Fn102bd0.frameInfo
      (fun fr => [span (fr.rdi + 16) 16]) _ _ hmultiply mem args ret low htypes h39 h50 h51 hdf
      (by simpa only [hsp] using hread) (by simpa only [hsp] using hret) hretlow
      (fun _ => by
        change Writable code mem (args[4].get 64 - 128) 128
        rw [hsp]
        exact hstack) (by
        change low.toNat + 128 ≤ (args[4].get 64).toNat
        rw [hsp]
        exact hroom)
      (by simpa only [hsp] using halign) (by trivial)
      (by simpa only [activationOfValues, callStack, hsp, hdst] using And.intro hw hsep)
  change o.values[4] = ⟨64, args[4].get 64 + 8⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
    o.values[3] = ⟨64, args[3].get 64⟩ ∧ o.values[5] = ⟨64, args[5].get 64⟩ ∧
    o.values[12] = ⟨64, args[12].get 64⟩ ∧ o.values[13] = ⟨64, args[13].get 64⟩ ∧
    o.values[14] = ⟨64, args[14].get 64⟩ ∧ o.values[15] = ⟨64, args[15].get 64⟩ ∧
    o.values[39] = ⟨32, args[39].get 32⟩ ∧ o.values[50] = ⟨16, args[50].get 16⟩ ∧
    o.values[51] = ⟨16, args[51].get 16⟩ ∧ True at hdone
  rcases hdone with ⟨h4, h22, h3, h5, h12, h13, h14, h15, hf39, hf50, hf51, -⟩
  refine ⟨o, hexec, htag, ?_, ?_, houtTypes, ?_, ?_⟩
  · simpa only [hsp] using h4
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3.trans (htypes.value ⟨3, by decide⟩).symm
    · exact h5.trans (htypes.value ⟨5, by decide⟩).symm
    · exact h12.trans (htypes.value ⟨12, by decide⟩).symm
    · exact h13.trans (htypes.value ⟨13, by decide⟩).symm
    · exact h14.trans (htypes.value ⟨14, by decide⟩).symm
    · exact h15.trans (htypes.value ⟨15, by decide⟩).symm
    · exact h22.trans hdf.symm
    · exact hf39.trans h39.symm
    · exact hf50.trans h50.symm
    · exact hf51.trans h51.symm
  · simpa only [activationOfValues, Activation.region, hsp, hdst] using hframe
  · simpa only [activationOfValues, hdst] using hpost

theorem multiply_pushed (code : CodeMap) (hmultiply : MultiplyContract code)
    (mem : Ram) (args : Values Value Reg.count) (sp dst ret low : BitVec 64)
    (hsp : args[4].get 64 = sp - 8) (hdst : args[7].get 64 = dst)
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hdf : args[22] = ⟨1, 0⟩)
    (hretlow : ret.toNat < 2^32) (hstack : Writable code mem (sp - 136) 136)
    (hroom : low.toNat + 136 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32)) :
    ∃ o : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨⟨.l102bd0, args, memStore mem (sp - 8) ret⟩, []⟩ o ∧
      o.tag = some ⟨64, ret⟩ ∧ o.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values ∧
      RamWriteFrame mem o.store [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := polyvalMultiplyWords
          (args[6].get 64 ^^^ memLoad mem (dst + 16) 64)
          (args[2].get 64 ^^^ memLoad mem (dst + 24) 64)
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
       memLoad o.store (dst + 16) 64 = result.1 ∧ memLoad o.store (dst + 24) 64 = result.2) := by
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by
    have hle : (8 : BitVec 64) ≤ sp := by change 8 ≤ sp.toNat; omega
    simpa using BitVec.toNat_sub_of_le hle
  have hsread : Readable mem (sp - 8) 8 := by
    apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have pushedFrame : RamWriteFrame mem (memStore mem (sp - 8) ret)
      [⟨low.toNat, sp.toNat - low.toNat⟩] := by
    apply (RamWriteFrame.refl _ _).memStore ret
    refine ⟨⟨low.toNat, sp.toNat - low.toNat⟩, by simp, ?_⟩
    simp only [InRegion, hsub]
    have := sp.isLt
    omega
  have hdsep := disjoint_bounds low.toNat (sp.toNat - low.toNat)
    dst.toNat 32 (by omega) (by decide) hsep
  have hload (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad (memStore mem (sp - 8) ret) (dst + BitVec.ofNat 64 off) 64 =
        memLoad mem (dst + BitVec.ofNat 64 off) 64 := by
    apply pushedFrame.memLoad_eq
    have haddr : (dst + BitVec.ofNat 64 off).toNat = dst.toNat + off := by
      have := hw.readable.low
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨by have := hw.readable.low; rw [haddr]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [haddr]
    dsimp only
    omega
  have hl0 : memLoad (memStore mem (sp - 8) ret) dst 64 = memLoad mem dst 64 := by
    simpa using hload 0 (by decide)
  have hl8 : memLoad (memStore mem (sp - 8) ret) (dst + 8) 64 = memLoad mem (dst + 8) 64 :=
    hload 8 (by decide)
  have hl16 : memLoad (memStore mem (sp - 8) ret) (dst + 16) 64 = memLoad mem (dst + 16) 64 :=
    hload 16 (by decide)
  have hl24 : memLoad (memStore mem (sp - 8) ret) (dst + 24) 64 = memLoad mem (dst + 24) 64 :=
    hload 24 (by decide)
  obtain ⟨o, hexec, htag, houtsp, hregs, houttypes, hf, hpost⟩ :=
    multiply_values code hmultiply (memStore mem (sp - 8) ret) args (sp - 8) dst ret low
      hsp hdst htypes h39 h50 h51 hdf (hsread.memStore _ _)
      (memLoad_memStore_same _ _ _ (by decide) (by decide)) hretlow
      (by have he : sp - 8 - 128 = sp - 136 := by bv_omega
          rw [he]
          exact (hstack.memStore _ _).sub (Nat.le_refl _) (by omega))
      (by rw [hsub]; omega) (by rw [hsub]; omega) (hw.memStore _ _)
      (by simpa only [hsub, show sp.toNat - 8 + 8 - low.toNat = sp.toNat - low.toNat by omega]
          using hsep)
  refine ⟨o, hexec, htag, ?_, hregs, houttypes, ?_, ?_⟩
  · have he : sp - 8 + 8 = sp := by bv_omega
    simpa only [he] using houtsp
  · have hp : RamWriteFrame mem (memStore mem (sp - 8) ret)
        [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] := by
      exact (RamWriteFrame.refl _ _).trans pushedFrame
        (by intro r hr; exact ⟨r, List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)), Nat.le_refl _, Nat.le_refl _⟩)
    apply hp.trans hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨⟨low.toNat, sp.toNat - low.toNat⟩, by simp, Nat.le_refl _, ?_⟩
      dsimp only
      rw [hsub]
      omega
    · exact ⟨span (dst + 16) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  · simpa only [hl0, hl8, hl16, hl24] using hpost


end AesGcm.Proofs.Machine.GHASHUpdate
