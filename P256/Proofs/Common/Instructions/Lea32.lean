import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Lea.Decode
import X86Proofs.Instructions.MovLoad.Step
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.MovStore.Decode

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Lea32

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem lea_r32_m_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (hsize : ctx.operand_size = 32)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (hmode : In64BitMode t) :
    (X86.Instructions.LEA_GPRv_AGEN ip ctx mod reg rm).run s =
      (.ok (), writeResult t (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32) (addr.setWidth 32)
        next) := by
  have hcontext :
      {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LEA_GPRv_AGEN
  simp only [writeResult, Operand.write_reg32]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [MonadState.get => get_run _]
  refine (writeGPR32_run _ _ _ (hmode.of_cs_lma_eq (t := {t with Next_IP := next}) rfl rfl)).trans ?_
  rfl

theorem decodeLegacy0_run_of_8D_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x8D :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x8D :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.LEA_GPRv_AGEN (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode8D _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode8D_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem lea_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x8D :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult t dst ((am.addrAt s (3 + am.tail.length)).setWidth 32)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (rex :: 0x8D :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_rex_8D s h rex (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x8D :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j _ => getElem?_cons3 _ _ _ _ j) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) =
      am.addrAt s (3 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [haddr] at hrip
  rw [lea_r32_m_form _ t _ _ _ _ _ (hrex.operand_size s.DS) rfl rfl _ _ _ _ _ hea hrip hmode]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x8D _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem lea_r32_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x8D :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeResult t dst ((am.addrAt s (2 + am.tail.length)).setWidth 32)
        (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (0x8D :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_8D_memory s h (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x8D :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j _ => by simp only [show 2 + j = j + 1 + 1 by omega, List.getElem?_cons_succ]) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 3 + am.tail.length = 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) =
      am.addrAt s (2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)))
  rw [haddr] at hrip
  rw [lea_r32_m_form _ t _ _ _ _ _ rfl rfl rfl _ _ _ _ _ hea hrip hmode]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x8D _
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def leaR32Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (len : Nat)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((am.addr s (p + BitVec.ofNat 64 len)).setWidth 32).setWidth 64⟩] }

theorem lea_r32_effect_step_of_run [Bindings] (p : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (len : Nat) (bytes : List UInt8)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → s.RIP = p →
      Machine.step s = some (.next (afterStep s len fun t =>
        writeResult t (.reg dst : Operand 32) ((am.addrAt s len).setWidth 32)
          (p + BitVec.ofNat 64 len)))) :
    StepEffect (fun s => s.RIP = p) (codeRange p bytes) (leaR32Effect p dst am len) := by
  rintro s h hcode rfl
  refine ⟨_, hstep s h hcode rfl, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  rfl

theorem lea_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am (3 + am.tail.length)) := by
  apply lea_r32_effect_step_of_run
  rintro s h hcode rfl
  apply lea_r32_step s h rex hrex reg am hv hx hb hcode.bytesAt
  have := am.tail_length_le
  have := hcode.low (by simp) (by simp; omega)
  simp only [List.length_cons] at this
  omega

theorem lea_r32_legacy_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x8D :: am.modrm reg :: am.tail))
      (leaR32Effect p (gprNumber 0 0 reg) am (2 + am.tail.length)) := by
  apply lea_r32_effect_step_of_run
  rintro s h hcode rfl
  apply lea_r32_legacy_step s h reg am hv hx hb hcode.bytesAt
  have := am.tail_length_le
  have := hcode.low (by simp) (by simp; omega)
  simp only [List.length_cons] at this
  omega

theorem lea_ecx_rax_sub2_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x8D, 0x48, 0xFE])
      (leaR32Effect p 1 (.base 0 (.d8 0xFE)) 3) :=
  lea_r32_legacy_effect_step p 1 (.base 0 (.d8 0xFE))
    (by simp [AddrMode.Valid, regLow]) rfl rfl

theorem lea_eax_r14_add1_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0x8D, 0x46, 0x01])
      (leaR32Effect p 0 (.base 14 (.d8 1)) 4) :=
  lea_r32_effect_step p 0x41 (by simp [RexNoWPrefix]) 0 (.base 14 (.d8 1))
    (by simp [AddrMode.Valid, regLow]) rfl rfl

end P256.Proofs.Common.Instructions.Lea32
