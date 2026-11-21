import X86Proofs.Step.Escape
import X86Proofs.Step.FetchImm

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def SupportedOpcode (opcode : UInt8) : Prop := opcode = 0x92 ∨ opcode = 0x94

theorem decodeLegacy1_run_of_setccOpcode [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (opcode : UInt8) (hop : SupportedOpcode opcode)
    (hrex2 : context.rex2_prefix_present = false) (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok opcode.toBitVec, t)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_92 ip context opcode.toBitVec).run t) := by
  rcases hop with rfl | rfl
  all_goals
    unfold Decode_Legacy_1
    rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
    rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
    repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
    repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
    rfl

theorem selectLegacy1Opcode92_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_92 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_92, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1Opcode92_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm opcode : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_92 ip context opcode).run s =
      (X86.Instructions.SETB_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3) opcode).run t := by
  unfold Decode_Legacy_1_Opcode_92
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode92_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy1_run_of_setcc [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm opcode : UInt8) (hop : SupportedOpcode opcode)
    (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hopbyte : bytes[k]? = some opcode) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.SETB_GPR8 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmRm modrm) opcode.toBitVec).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok opcode.toBitVec, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = opcode from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hopbyte)] at this
    exact this
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64) 8).run
      (afterFetches (beforeFetch s) (k + 2)) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) (k + 3)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 2) hf hc hlow (k + 1) hlen hk
    rw [show bytes[k + 1] = modrm from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hm)] at this
    rw [show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 1)) from add_ofNat_add s.RIP k 1]
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_setccOpcode _ _ _ _ opcode hop hrex2 (hmode _) f1,
    decodeLegacy1Opcode92_run_of_register _ _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

end P256.Proofs.Common.Instructions.Setb
