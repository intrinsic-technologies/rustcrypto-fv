import P256.Proofs.Common.Memory.Fill.Stos.Spec

namespace P256.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess

theorem repStosAfter_external (bytes len : Nat) (s : RamState) :
    (repStosAfter bytes len s).external =
      memStore s.external (rdi.read s) ((Operand.reg 0 : Operand (8 * bytes)).read s) := rfl

theorem repStosAfter_gpr (bytes len : Nat) (s : RamState) :
    (repStosAfter bytes len s).GPR =
      Vector.set (Vector.set s.GPR 7 (BitVec.add s.GPR[7] (BitVec.ofNat 64 bytes))) 1 (s.GPR[1] - 1) := by
  simp only [repStosAfter, afterStep, finishStep, repCount, Operand.write, stosSpec, dataAccess,
    afterFetches, beforeFetch, resetStepFields, BitVec.ofNat_eq_ofNat, Int.reduceToNat,
    BitVec.add_eq, Operand.read, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Fin.reduceFinMk, Fin.getElem_fin, Fin.isValue, BitVec.setWidth_eq, Nat.zero_mod,
    Fin.zero_eta, Nat.reduceAdd, Fin.val_zero, mergeGPR_64, Nat.one_mod, Fin.mk_one,
    Fin.val_one, Vector.getElem_set, Bool.not_false, Bool.not_not, Bool.true_and,
    Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  rfl

theorem repStosAfter_rdi (bytes len : Nat) (s : RamState) :
    rdi.read (repStosAfter bytes len s) = rdi.read s + BitVec.ofNat 64 bytes := by
  simp only [Operand.read, Int.reduceToNat, repStosAfter_gpr, BitVec.add_eq,
    BitVec.ofNat_eq_ofNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Fin.reduceFinMk, Fin.getElem_fin, Fin.isValue, Vector.getElem_set, BitVec.setWidth_eq]
  rfl

theorem repStosAfter_rcx (bytes len : Nat) (s : RamState) :
    rcx.read (repStosAfter bytes len s) = rcx.read s - 1 := by
  simp [Operand.read, repStosAfter_gpr, gprIndex]

theorem rcx_read_stosSpec (bytes : Nat) (t : RamState) :
    rcx.read (stosSpec bytes t) = rcx.read t := by
  simp only [stosSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_reg_write_mem,
    Operand.read_reg_dataAccess]

theorem repStosAfter_repeat (bytes len : Nat) (s : RamState) :
    (repStosAfter bytes len s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repStosAfter, afterStep, finishStep, repCount, rcx_read_stosSpec]
  rfl

theorem repStosAfter_rip (bytes len : Nat) (s : RamState)
    (hmsr : s.«MSRLIST::In_Process» = false) :
    (repStosAfter bytes len s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 len) else s.RIP := by
  simp only [repStosAfter, afterStep, finishStep, repCount, rcx_read_stosSpec]
  simp [stosSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repStosAfter_agrees (bytes len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) bytes, .rip] (clearRep s)
      (clearRep (repStosAfter bytes len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repStosAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h7]
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [clearRep_external]
    rw [repStosAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) bytes) (by simp) ⟨i, by omega, he.symm⟩
  · simp only [fixedPart, clearRep, repStosAfter, repCount, afterStep, finishStep, stosSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repStosAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem repStosAfter_ready [Bindings] {s : RamState} (bytes len : Nat) (h : ReadyMidRep s)
    (hdst : (rdi.read s).toNat + bytes ≤ 2^32)
    (htables : (rdi.read s).toNat + bytes ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat) :
    ReadyMidRep (repStosAfter bytes len s) := by
  have htab : IdentityPageTableMemory (clearRep (repStosAfter bytes len s)).external := by
    rw [clearRep_external, repStosAfter_external]
    exact IdentityPageTableMemory.memStore (ReadyToStep.memory (s := clearRep s) h).tables _ _
      (by omega) (by omega)
  exact ReadyToStep.of_agreesExcept h.clear (repStosAfter_agrees bytes len s) htab

theorem repStosAfter_fill (bytes len : Nat) (s : RamState) (hbytes : bytes ≤ 8)
    (hzero : (Operand.reg 0 : Operand (8 * bytes)).read s = 0)
    (i : Nat) (hi : i < bytes) :
    (repStosAfter bytes len s).external[rdi.read s + BitVec.ofNat 64 i]? = some 0 := by
  rw [repStosAfter_external, hzero, memStore_getElem?_self _ _ _ (by omega) i (by omega)]
  simp [storedByte]

theorem repStosZeroAfter_rip (len : Nat) (s : RamState)
    (hmsr : s.«MSRLIST::In_Process» = false) :
    (repStosZeroAfter len s).RIP = BitVec.add s.RIP (BitVec.ofNat 64 len) := by
  simp [repStosZeroAfter, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repStosZeroAfter_repeat (len : Nat) (s : RamState) :
    (repStosZeroAfter len s).Repeat_String_Operation = false := rfl

theorem repStosZeroAfter_agrees (len : Nat) (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repStosZeroAfter len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, clearRep, repStosZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

end P256.Proofs.Common.Memory.Fill.Stos
