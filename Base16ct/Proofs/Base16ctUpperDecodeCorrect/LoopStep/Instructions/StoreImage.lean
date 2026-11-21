import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.MovStore8
import X86Proofs.Instructions.MovStore.Decode
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions.StoreImage
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem selectStore88 (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_88 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_88, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeStore88 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_88 ip context).run s =
      (X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_88
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_88 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectStore88 context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  rw [specM_bind_pure_unit_run]
  have h64 : Int.toNat 64 = 64 := by decide
  have h6 : Int.toNat 6 = 6 := by decide
  have h3 : Int.toNat 3 = 3 := by decide
  have h0 : Int.toNat 0 = 0 := by decide
  have h62 : (7 - 6 + 1 : Int).toNat = 2 := by decide
  have h53 : (5 - 3 + 1 : Int).toNat = 3 := by decide
  have h20 : (2 - 0 + 1 : Int).toNat = 3 := by decide
  change (X86.Instructions.MOV_MEMb_GPR8_1 (ip + 2#64) context
      (modrm.extractLsb' 6 2) (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t = _
  rfl

theorem decodeLegacy0_run_of_88 [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hcode : BytesAt s s.RIP [0x88, modrm, 0x01])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x88, modrm, 0x01] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x88, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run
      (afterFetches (beforeFetch s) 2) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) := by
    exact memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have hd : (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run
      (afterFetches (beforeFetch s) 1) =
      some ((Decode_Legacy_0_Opcode_88 s.RIP (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2)) := by
    unfold Decode_Legacy_0
    rw [ite_eq_right (fun h' => Bool.false_ne_true (by
      have hctx : (legacyContext s.DS).rex2_prefix_present = false := by rfl
      exact hctx.symm.trans h'))]
    rw [partialSpecM_liftTotal_bind_run _ _ f1]
    repeat erw [decodeLegacy0_modeGuard_run _ _ (hmode 2)]
    rfl
  rw [hd, decodeStore88 _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl
end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions.StoreImage

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions.StoreImage
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def lowerStoreAM : AddrMode := .sib 1 (some 0) 0#2 .none

theorem mov_lower_store_step_exact [Bindings] (p : BitVec 64) (s : RamState)
    (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0x88, 0x1c, 0x01]) s)
    (hpre : StorePre p 3 (fun s => lowerStoreAM.addrAt s 3) 1 s) :
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult (dataAccess t "store") (.mem (lowerStoreAM.addrAt s 3) : Operand 8)
        ((Operand.reg 3 : Operand 8).read s) (BitVec.add p 3#64))) := by
  obtain ⟨hp, hw, _⟩ := hpre
  change MemWritable s (lowerStoreAM.addrAt s 3) 1 at hw
  subst hp
  have hlow' : s.RIP.toNat + [0x88, 0x1c, 0x01].length ≤ 2^32 := by
    simpa using hcode.low (by simp) (by simp)
  have hdecode := decodeLegacy0_run_of_88 s h 0x1c
    (by decide) hcode.bytesAt hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x88, 0x1c, 0x01] := hcode.bytesAt
  have htail : lowerStoreAM.tail = [0x01] := by decide
  have htailLen : lowerStoreAM.tail.length = 1 := by decide
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss lowerStoreAM
    (by decide) (legacyContext s.DS) (AddrContext.legacy _ lowerStoreAM (by decide) (by decide))
    hc hlow' 2 (fun j hj => by
      simpa [htail] using (getElem?_cons2_append 0x88 0x1c [0x01] [] j hj))
      (by simp [htailLen]) (by simp [htailLen])
  let u := afterFetches (beforeFetch s) (3 + lowerStoreAM.tail.length)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + lowerStoreAM.tail.length))) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (3 + lowerStoreAM.tail.length)) := by
    have hx := add_ofNat_add s.RIP (2 + lowerStoreAM.tail.length) 1
    rw [show 2 + lowerStoreAM.tail.length + 1 = 3 + lowerStoreAM.tail.length by omega] at hx
    exact hx
  have hrip := handleRIPRelativeAddress_addrMode_run lowerStoreAM (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + lowerStoreAM.tail.length))) 1#64)
  rw [show lowerStoreAM.addr (beforeFetch s) _ = lowerStoreAM.addrAt s (3 + lowerStoreAM.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  have hea' : (Effective_Address 64 (legacyContext s.DS) lowerStoreAM.mod lowerStoreAM.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (lowerStoreAM.offset (beforeFetch s), flatData lowerStoreAM.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + lowerStoreAM.tail.length)), lowerStoreAM.isRip, lowerStoreAM.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + lowerStoreAM.tail.length)) := hea
  have hform := Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions.mov_m8_r8_form
    (s := afterFetches (beforeFetch s) 3) (t := u) (ip := BitVec.add s.RIP 2#64)
    (ctx := legacyContext s.DS) (mod := lowerStoreAM.mod) (reg := 3#3) (rm := lowerStoreAM.rm)
    rfl rfl (off := lowerStoreAM.offset (beforeFetch s))
    (next := BitVec.add s.RIP 3#64) (addr := lowerStoreAM.addrAt s 3)
    (isStack := lowerStoreAM.isStack) (isRip := lowerStoreAM.isRip) hea' hrip hu
    (hw.of_external_eq rfl) hmode (by change (3#5).toNat < 4; decide)
  have hmodField : modrmMod (0x1c : UInt8) = lowerStoreAM.mod := by decide
  have hregField : modrmReg (0x1c : UInt8) = 3#3 := by decide
  have hrmField : modrmRm (0x1c : UInt8) = lowerStoreAM.rm := by decide
  rw [hmodField, hregField, hrmField] at hdecode
  have hdecode' : (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run
      (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) lowerStoreAM.mod (3#3) lowerStoreAM.rm).run
        (afterFetches (beforeFetch s) 3)) := by
    simpa using hdecode
  have hgreg : gprNumber (legacyContext s.DS).rex_r4 (legacyContext s.DS).rex_r3 (3#3) = 3#5 := by
    change gprNumber 0 0 (3#3) = 3#5
    decide
  have hdecodeStep : (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run
      (afterFetches (beforeFetch s) 1) =
      some (.ok (), writeResult (dataAccess u "store")
        (.mem (lowerStoreAM.addrAt s 3) : Operand 8) (Operand.read s (Operand.reg 3 : Operand 8))
        (BitVec.add s.RIP 3#64)) := by
    rw [hdecode', hform]
    rw [hgreg]
    simp only [u, Operand.read_afterFetches, Operand.read_beforeFetch]
    simp [movSpec]
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0x88 [0x1c, 0x01]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode.bytesAt hlow' hdecodeStep
    (hmode.of_cs_lma_eq rfl rfl)

theorem mov_lower_store_step [Bindings] (p : BitVec 64) :
    StepEffect (StorePre p 3 (fun s => lowerStoreAM.addrAt s 3) 1)
      (codeRange p [0x88, 0x1c, 0x01])
      (storeEffect p 3 (fun s => lowerStoreAM.addrAt s 3)
        (fun s => (Operand.reg 3 : Operand 8).read s)) := by
  exact StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    (mov_lower_store_step_exact p)

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
