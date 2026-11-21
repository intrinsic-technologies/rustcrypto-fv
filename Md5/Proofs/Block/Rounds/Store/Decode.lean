import X86Proofs.Instructions.MovStore.Decode

namespace Md5.Proofs.Block.Rounds.Store

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_89_memory [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x89 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x89 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMv_GPRv_1 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode89 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode89_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl


end Md5.Proofs.Block.Rounds.Store
