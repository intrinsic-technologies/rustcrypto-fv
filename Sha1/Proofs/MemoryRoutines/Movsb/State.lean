import X86Proofs.Instructions.Movs.RepStep
import Sha1.Proofs.Compress.Machine.Memory
import Sha1.Proofs.Common.Instructions.MemoryWriteFrame

namespace Sha1.Proofs.MemoryRoutines.Movsb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs Sha1.Spec.Program

def repMovsbAfter (s : RamState) : RamState :=
  afterStep s 2 fun t => repCount (movsSpec 8 { t with Next_IP := BitVec.add s.RIP 2#64 })

def repMovsbZeroAfter (s : RamState) : RamState :=
  afterStep s 2 fun t =>
    { t with Next_IP := BitVec.add s.RIP 2#64, Repeat_String_Operation := false }

theorem repMovsbAfter_external (s : RamState) :
    (repMovsbAfter s).external =
      memStore s.external (rdi.read s) ((Operand.mem (rsi.read s) : Operand 8).read s) := rfl

theorem repMovsbAfter_rflags (s : RamState) : (repMovsbAfter s).RFLAGS = s.RFLAGS := rfl

theorem repMovsbAfter_gpr (s : RamState) :
    (repMovsbAfter s).GPR = Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + 1)) 7
      (s.GPR[7] + 1)) 1 (s.GPR[1] - 1) := by
  simp only [repMovsbAfter, afterStep, finishStep, repCount, Operand.write, movsSpec,
    dataAccess, afterFetches, beforeFetch, resetStepFields, BitVec.ofNat_eq_ofNat,
    Int.reduceToNat, Nat.reduceAdd, Nat.reduceMul, BitVec.add_eq, Operand.read, gprIndex,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk, Fin.getElem_fin,
    Fin.isValue, BitVec.setWidth_eq, Nat.zero_lt_succ, Nat.div_self, mergeGPR_64,
    Vector.getElem_set, Nat.one_mod, Fin.mk_one, Fin.val_one, Bool.not_false, Bool.not_not,
    Bool.true_and, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  rfl

theorem repMovsbAfter_rsi (s : RamState) : rsi.read (repMovsbAfter s) = rsi.read s + 1 := by
  simp only [Operand.read, Int.reduceToNat, repMovsbAfter_gpr, BitVec.ofNat_eq_ofNat,
    gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
    Fin.getElem_fin, Fin.isValue, Vector.getElem_set, BitVec.setWidth_eq]
  rfl

theorem repMovsbAfter_rdi (s : RamState) : rdi.read (repMovsbAfter s) = rdi.read s + 1 := by
  simp only [Operand.read, Int.reduceToNat, repMovsbAfter_gpr, BitVec.ofNat_eq_ofNat,
    gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
    Fin.getElem_fin, Fin.isValue, Vector.getElem_set, BitVec.setWidth_eq]
  rfl

theorem repMovsbAfter_rcx (s : RamState) : rcx.read (repMovsbAfter s) = rcx.read s - 1 := by
  simp [Operand.read, repMovsbAfter_gpr, gprIndex]

theorem repMovsbAfter_repeat (s : RamState) :
    (repMovsbAfter s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repMovsbAfter, afterStep, finishStep, repCount, rcx_read_movsSpec]
  rfl

theorem repMovsbAfter_rip (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsbAfter s).RIP = if rcx.read s - 1 = 0 then BitVec.add s.RIP 2#64 else s.RIP := by
  simp only [repMovsbAfter, afterStep, finishStep, repCount, rcx_read_movsSpec]
  simp [movsSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem AgreesExcept.repMovsb (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) 1, .rip] (clearRep s)
      (clearRep (repMovsbAfter s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repMovsbAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6,
        Ne.symm h7]
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | df => rfl
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
  · simp only [clearRep_external]
    rw [repMovsbAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) 1) (by simp) ⟨i, by omega, he.symm⟩
  · simp only [fixedPart, clearRep, repMovsbAfter, repCount, afterStep, finishStep, movsSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repMovsbAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem readyMidRep_repMovsb [Bindings] {s : RamState} (h : ReadyMidRep s)
    (htables : ∀ i < 1, ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)) :
    ReadyMidRep (repMovsbAfter s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsbAfter s)).external := by
    rw [clearRep_external, repMovsbAfter_external]
    exact Sha1.Proofs.Common.Instructions.MemoryWriteFrame.identityPageTableMemory_memStore
      (ReadyToStep.memory (s := clearRep s) h).tables _ _ htables
  exact ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovsb s) htab

theorem repMovsbAfter_copy (s : RamState) (i : Nat) (hi : i < 1)
    (hsrc : (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome) :
    (repMovsbAfter s).external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rw [repMovsbAfter_external, memStore_getElem?_self _ _ _ (by decide) i (by omega)]
  simp only [Operand.read]
  rw [storedByte_memLoad _ _ i (by omega), memByte]
  simp only [PhysicalMemory.read]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsrc
  change some ((s.external[rsi.read s + BitVec.ofNat 64 i]?).getD 0) =
    s.external[rsi.read s + BitVec.ofNat 64 i]?
  rw [hb]
  rfl

theorem repMovsbZeroAfter_external (s : RamState) :
    (repMovsbZeroAfter s).external = s.external := rfl

theorem repMovsbZeroAfter_rip (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsbZeroAfter s).RIP = BitVec.add s.RIP 2#64 := by
  simp [repMovsbZeroAfter, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repMovsbZeroAfter_repeat (s : RamState) :
    (repMovsbZeroAfter s).Repeat_String_Operation = false := rfl

theorem AgreesExcept.repMovsbZero (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repMovsbZeroAfter s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | df => rfl
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
  · simp only [fixedPart, clearRep, repMovsbZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

end Sha1.Proofs.MemoryRoutines.Movsb
