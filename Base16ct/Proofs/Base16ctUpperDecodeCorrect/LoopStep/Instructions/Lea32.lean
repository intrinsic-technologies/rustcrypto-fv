import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem lea32_operation (x : BitVec 64) :
    X86.Instructions.Operations.LEA 32 x = .ok (x.extractLsb' 0 32) := by
  simp [X86.Instructions.Operations.LEA, x86_runtime, bind, pure, Except.bind, Except.pure]

theorem lea_r32_m_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (hmode : In64BitMode t) (hsize : ctx.operand_size = 32)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.LEA_GPRv_AGEN ip ctx mod reg rm).run s =
      (.ok (), writeResult t (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32)
        (addr.extractLsb' 0 32) next) := by
  have hcontext :
      {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LEA_GPRv_AGEN
  simp only [lea32_operation, writeResult, Operand.write_reg32]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [MonadState.get => get_run _]
  refine (writeGPR32_run _ _ _ (hmode.of_cs_lma_eq (t := {t with Next_IP := next}) rfl rfl)).trans ?_
  rfl

theorem lea_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x8D :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult t dst ((am.addrAt s (3 + am.tail.length)).extractLsb' 0 32)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (rex :: 0x8D :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]
    have := am.tail_length_le
    omega
  have hdecode := decodeLegacy0_run_of_rex_8D s h rex (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x8D :: am.modrm reg :: am.tail) := hcode
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
  rw [lea_r32_m_form (s := afterFetches (beforeFetch s) 4) (t := t)
    (ip := BitVec.add s.RIP 3#64) (ctx := rexContext s.DS rex.toBitVec)
    (mod := am.mod) (reg := reg) (rm := am.rm)
    (off := am.offset (beforeFetch s))
    (next := BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
    (addr := am.addrAt s (3 + am.tail.length)) (seg := flatData am.isStack) (isRip := am.isRip)
    hea hrip hmode (hrex.operand_size s.DS) rfl rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x8D _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def leaR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (am.addr s (p + BitVec.ofNat 64 len)).extractLsb' 0 32 |>.setWidth 64⟩] }

@[simp] theorem leaR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (leaR32Effect p len dst am s).components = [.reg dst, .rip] := rfl

theorem lea_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode rfl
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, lea_r32_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => (am.addrAt s (3 + am.tail.length)).extractLsb' 0 32) _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]
  rfl

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
