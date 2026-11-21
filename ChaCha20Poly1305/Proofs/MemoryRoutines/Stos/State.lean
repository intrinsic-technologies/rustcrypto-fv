import ChaCha20Poly1305.Proofs.MemoryRoutines.Stos.Model
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import ChaCha20Poly1305.Proofs.MemoryRoutines.Instructions.MemoryWriteFrame

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Common

theorem Kind.bytes_pos (kind : Kind) : 0 < kind.bytes := by cases kind <;> decide

theorem Kind.bytes_le (kind : Kind) : kind.bytes ≤ 8 := by cases kind <;> decide

theorem repStosAfter_external (kind : Kind) (s : RamState) :
    (repStosAfter kind s).external =
      memStore s.external (rdi.read s) ((Operand.reg 0 : Operand (8 * kind.bytes)).read s) := rfl

theorem repStosAfter_rflags (kind : Kind) (s : RamState) :
    (repStosAfter kind s).RFLAGS = s.RFLAGS := rfl

theorem repStosAfter_gpr (kind : Kind) (s : RamState) :
    (repStosAfter kind s).GPR =
      Vector.set (Vector.set s.GPR 7 (BitVec.add s.GPR[7] (BitVec.ofNat 64 kind.bytes)))
        1 (s.GPR[1] - 1) := by
  simp [repStosAfter, repCount, afterStep, finishStep, stosSpec, Operand.write, Operand.read,
    dataAccess, afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64,
    Vector.getElem_set]
  rfl

theorem repStosAfter_rdi (kind : Kind) (s : RamState) :
    rdi.read (repStosAfter kind s) = rdi.read s + BitVec.ofNat 64 kind.bytes := by
  simp [Operand.read, repStosAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repStosAfter_rcx (kind : Kind) (s : RamState) :
    rcx.read (repStosAfter kind s) = rcx.read s - 1 := by
  simp [Operand.read, repStosAfter_gpr, gprIndex]

theorem repStosAfter_rax (kind : Kind) (s : RamState) (n : Nat) :
    (Operand.reg 0 : Operand n).read (repStosAfter kind s) =
      (Operand.reg 0 : Operand n).read s := by
  simp [Operand.read, repStosAfter_gpr, gprIndex]

theorem rcx_read_stosSpec (n : Nat) (s : RamState) :
    rcx.read (stosSpec n s) = rcx.read s := by
  simp only [stosSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_reg_write_mem,
    Operand.read_reg_dataAccess]

theorem repStosAfter_repeat (kind : Kind) (s : RamState) :
    (repStosAfter kind s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repStosAfter, afterStep, finishStep, repCount, rcx_read_stosSpec]
  rfl

theorem repStosAfter_rip (kind : Kind) (s : RamState)
    (hmsr : s.«MSRLIST::In_Process» = false) :
    (repStosAfter kind s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length) else s.RIP := by
  simp only [repStosAfter, afterStep, finishStep, repCount, rcx_read_stosSpec]
  simp [stosSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repStosAfter_agrees (kind : Kind) (s : RamState) :
    AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) kind.bytes, .rip]
      (clearRep s) (clearRep (repStosAfter kind s)) := by
  refine ⟨fun c hc hm ↦ ?_, fun x hx ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h ↦ hc (by simp [h])
      have h7' : r ≠ 7 := fun h ↦ hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e ↦ h1' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e ↦ h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repStosAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h7]
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
    rw [repStosAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) kind.bytes) (by simp) ⟨i, by omega, he.symm⟩
  · simp only [fixedPart, clearRep, repStosAfter, repCount, afterStep, finishStep, stosSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repStosAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem repStosAfter_ready [Bindings] {s : RamState} (kind : Kind) (h : ReadyMidRep s)
    (htables : ∀ i < kind.bytes, ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)) :
    ReadyMidRep (repStosAfter kind s) := by
  have htab : IdentityPageTableMemory (clearRep (repStosAfter kind s)).external := by
    rw [clearRep_external, repStosAfter_external]
    exact ChaCha20Poly1305.Proofs.MemoryRoutines.Instructions.MemoryWriteFrame.identityPageTableMemory_memStore
      (ReadyToStep.memory (s := clearRep s) h).tables _ _ (by simpa using htables)
  exact ReadyToStep.of_agreesExcept h.clear (repStosAfter_agrees kind s) htab

theorem repStosAfter_fill (kind : Kind) (s : RamState) (i : Nat) (hi : i < kind.bytes) :
    (repStosAfter kind s).external[rdi.read s + BitVec.ofNat 64 i]? =
      some (storedByte ((Operand.reg 0 : Operand (8 * kind.bytes)).read s) i) := by
  rw [repStosAfter_external, memStore_getElem?_self _ _ _ (by
    have := kind.bytes_le; omega) i (by omega)]

theorem repStosZeroAfter_external (kind : Kind) (s : RamState) :
    (repStosZeroAfter kind s).external = s.external := rfl

theorem repStosZeroAfter_rip (kind : Kind) (s : RamState)
    (hmsr : s.«MSRLIST::In_Process» = false) :
    (repStosZeroAfter kind s).RIP = BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length) := by
  simp [repStosZeroAfter, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repStosZeroAfter_repeat (kind : Kind) (s : RamState) :
    (repStosZeroAfter kind s).Repeat_String_Operation = false := rfl

theorem repStosZeroAfter_agrees (kind : Kind) (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repStosZeroAfter kind s)) := by
  refine ⟨fun c hc hm ↦ ?_, fun _ _ ↦ rfl, ?_, fun _ h ↦ h⟩
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
  · simp only [fixedPart, clearRep, repStosZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

end ChaCha20Poly1305.Proofs.MemoryRoutines.Stos
