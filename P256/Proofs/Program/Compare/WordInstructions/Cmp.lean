import P256.Proofs.Common.Instructions.CompareWord
import X86Proofs.Program.Compose

namespace P256.Proofs.Program.Compare.WordInstructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def cmpR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg dst : Operand 16).read s)
      ((Operand.reg src : Operand 16).read s))) }

attribute [x86_compose] cmpR16R16Effect

@[x86_local] theorem cmpR16R16Effect_local (p : BitVec 64) (len : Nat) (dst src : BitVec 5) :
    Effect.Local (cmpR16R16Effect p len dst src) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun s t h i _ => ?_, fun _ => by simp [cmpR16R16Effect]⟩
  simp only [cmpR16R16Effect, Effect.flag, h.read_reg]

theorem cmp_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x39, modrm])
      (cmpR16R16Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) :=
  P256.Proofs.Common.Instructions.CompareWord.cmp_r16_r16_effect_step p modrm hmod

theorem cmp_r16_r16_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x66, rex, 0x39, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 4 fun t =>
      writeFlagsOutputs t
        (cmpSpec
          ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read t)
          ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 16).read t))
        0 (BitVec.add s.RIP 4#64))) := by
  have fop : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0x39, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have fmod : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have hd := decodeLegacy0_run_of_opcode39 _ _ _ (oszRexContext s.DS rex.toBitVec) rfl fop (hm 4)
  rw [decodeLegacy0Opcode39_run_of_register _ _ _ _ _ hmod (hm 5) hf fmod,
    P256.Proofs.Common.Instructions.CompareWord.cmp_r16_r16_form _ _ _ _ _ (hm 5)
      (hrex.operand_size_osz s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64] at hd
  have hpre : ∀ p ∈ [0x66, rex], ScanPrefix p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact scanPrefix_66
    · exact hrex.rexPrefix.scanPrefix
  have hd' : (Decode_Legacy_0 (BitVec.add s.RIP 2#64)
      (scanContext s.DS (PrefixSegments.ofState s) [0x66, rex])).run (afterFetches (beforeFetch s) 3) =
      some (.ok (), writeFlagsOutputs (afterFetches (beforeFetch s) 5)
        (cmpSpec
          ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s)
          ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 16).read s))
        0 (BitVec.add s.RIP 4#64)) := by
    rw [scanContext_66_rex s.DS (PrefixSegments.ofState s) hrex.rexPrefix]
    exact hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h [0x66, rex] 0x39 [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by simp) hcode hlow hd'
    ((hm 5).of_cs_lma_eq rfl rfl)

theorem cmp_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, 0x39, modrm])
      (cmpR16R16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r16_r16_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeFlagsOutputs h 4 _ 0 _,
    ⟨afterStep_writeFlagsOutputs_rip h 4 _ 0 _, trivial,
      StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 0 _⟩⟩

end P256.Proofs.Program.Compare.WordInstructions
