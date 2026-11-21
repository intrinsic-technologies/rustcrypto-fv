import P256.Proofs.Common.Encoding.Parser.ResultTag.Cmove
import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR32R32Value cmov_r32_r32_form decodeLegacy1Opcode42_run_of_register)

namespace P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.SignedNormalize

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def cmoveR32R32RexEffect (p : BitVec 64) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), (cmovR32R32Value 4 dst src s).setWidth 64⟩] }

theorem cmove_r32_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexNoWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0x44, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst := gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)
    let src := gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg dst)
        (cmovR32R32Value 4 dst src t) (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0f, 0x44, modrm] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := P256.Proofs.Common.Encoding.Parser.ResultTag.decodeLegacy1_run_of_cmove _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS rex.toBitVec) rfl (hmode 4) f1
  rw [decodeLegacy1Opcode42_run_of_register _ _ _ _ _ _ hmod (hmode 5) hf f2,
    cmov_r32_r32_form _ _ _ _ _ _ (hmode 5) (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x44 [modrm] hrex.rexPrefix
    (by decide) hcode hlow hd
    ((hmode 5).of_cs_lma_eq rfl rfl)

theorem cmove_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0x44, modrm])
      (cmoveR32R32RexEffect p
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmove_r32_r32_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  simp only [cmovR32R32Value, Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

@[x86_local_on] theorem cmoveR32R32RexEffect_localOn (p : BitVec 64) (dst src : BitVec 5) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.ZF] (cmoveR32R32RexEffect p dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t u ho hf
    have hz : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        (StatusFlags.ofRFLAGS u.RFLAGS).ZF := hf .ZF (by simp)
    simp [cmoveR32R32RexEffect, cmovR32R32Value, condHolds, ho.read_reg, hz]
  · intro t
    simp [cmoveR32R32RexEffect, Write.Full, Operand.Full]

attribute [x86_compose] cmoveR32R32RexEffect

end P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.SignedNormalize
