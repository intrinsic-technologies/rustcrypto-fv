import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.MovStore.Decode

namespace Md5.Proofs.Block.Rounds

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_8B_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x8B :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x8B :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_GPRv_MEMv_1 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode8B _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode8B_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem mov_r32_m32_noRex_step [Bindings] (s : RamState) (h : ReadyToStep s) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x8B :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (2 + am.tail.length)) 4) :
    let dst : Operand 32 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem (am.addrAt s (2 + am.tail.length)) : Operand 32).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (0x8B :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_8B_memory s h (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x8B :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j _ => by rw [show 2 + j = j + 1 + 1 by omega]; rfl)
    (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 3 + am.tail.length = 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) =
      am.addrAt s (2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)))
  rw [haddr] at hrip
  rw [mov_r_m_form _ t _ _ _ _ _ 32 (.inr rfl) (legacyContext_operand_size s.DS) rfl rfl _ _ _ _ _
    hea hrip _ (SegAccess.flat _ _) ht hmode hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x8B _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

@[x86_compose] def movR32M32NoRexEffect (p : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (2 + am.tail.length)
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length)))
        : Operand 32).read s).setWidth 64⟩] }

@[x86_local] theorem movR32M32NoRexEffect_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (movR32M32NoRexEffect p dst am) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · simp [movR32M32NoRexEffect, h.read_mem, AddrMode.addr_obs h]
  · simp [movR32M32NoRexEffect, h.read_mem, AddrMode.addr_obs h]
  · simp [movR32M32NoRexEffect, h.read_mem, AddrMode.addr_obs h]
  · cases i <;> simp_all [movR32M32NoRexEffect, Effect.flag,
      StatusFlags.get, h.read_mem, AddrMode.addr_obs h]
  · simp [movR32M32NoRexEffect, Write.Full, Operand.Full]

theorem mov_r32_m32_noRex_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x8B :: am.modrm reg :: am.tail))
      (movR32M32NoRexEffect p (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, mov_r32_m32_noRex_step s h reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

end Md5.Proofs.Block.Rounds
