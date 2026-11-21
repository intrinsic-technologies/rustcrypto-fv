import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode83

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_rex_83_r4 [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (rex :: 0x83 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.AND_GPRv_IMMb (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x83 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x83 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x83, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow' 2 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode83 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode83_run_of_r4_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem decodeLegacy0_run_of_83_r4 [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (0x83 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.AND_GPRv_IMMb (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x83 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0x83 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x83, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode83 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode83_run_of_r4_register _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl

end X86Proofs
