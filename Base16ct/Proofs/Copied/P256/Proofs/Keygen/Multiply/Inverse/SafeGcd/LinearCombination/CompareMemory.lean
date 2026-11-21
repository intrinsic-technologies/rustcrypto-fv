import Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CompareMemory
import Base16ct.Proofs.Copied.P256.Proofs.Common.EffectCompose
set_option autoImplicit false
open Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions (decodeLegacy0_run_of_83_r7_memory)

namespace Base16ct.Proofs.Copied.P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem cmp_m64_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64) = .ok addr)
    (hu : DataReady u) (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.CMP_MEMv_IMMb ip ctx mod rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess u "load")
        (cmpSpec ((Operand.mem addr : Operand 64).read u) (imm.signExtend 64)) 0
        (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  have hcontext :
      {ctx with address_size := 64, operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_MEMv_IMMb
  simp only [writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.CMP => cmp_operation _ 64 (by decide) _ _]

theorem cmp_m64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 8) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.mem addr : Operand 64).read t) (imm.toBitVec.signExtend 64)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])).length =
      pre.length + 3 + am.tail.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_83_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x83 7 am hv [imm] _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])) := hcode
  have hfetch := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3 + am.tail.length) h.fetchReady hc
    hlow' (pre.length + 2 + am.tail.length) (by rw [hlen']; omega) (by omega)
  have himm : (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]'
      (by rw [hlen']; omega) = imm := by
    have : (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]? =
        some imm := by rw [getElem?_pre_tail]; simp
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  rw [himm] at hfetch
  let u := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl,
    show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega,
    ← add_tail_imm] at hrip
  rw [cmp_m64_imm8_form _ _ u _ _ _ _ haddr hsize hlock _ _ _ _ _ _ hea hfetch hrip
    (memAlu_dataReady h _)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.low)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.mem)] at hdecode
  rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega] at hdecode
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x83 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def cmpM64Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s)
      (imm.signExtend 64))) }

theorem cmpM64Imm8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) :
    (cmpM64Imm8Effect p len am imm s).components = [.flags, .rip] := rfl

theorem cmp_m64_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x48 :: 0x83 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM64Imm8Effect p (4 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hrex : RexPrefix (0x48 : UInt8).toBitVec := by simp [RexPrefix]
  have hstep := cmp_m64_imm8_step s h [0x48] (by simpa using hrex.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl) am hv
    (by rw [scanContext_rex _ _ hrex]; exact AddrContext.rex _ _ am hx.symm hb.symm)
    imm hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _
@[x86_local] theorem cmpM64Imm8Effect_local (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (cmpM64Imm8Effect p len am imm) := by
  apply Base16ct.Proofs.Copied.P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [cmpM64Imm8Effect, AddrMode.addr_obs h, h.read_mem]
  · intro s
    simp [cmpM64Imm8Effect, Write.Full, Operand.Full]
attribute [x86_compose] cmpM64Imm8Effect
end Base16ct.Proofs.Copied.P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination
