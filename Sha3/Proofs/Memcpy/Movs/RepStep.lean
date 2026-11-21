import X86Proofs.Instructions.Movs.RepStep
import Sha3.Proofs.Stos
import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Agrees
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ReadWrite.Stack
import Sha3.Proofs.Movs
import Sha3.Proofs.Memcpy.Movs.RepForm


namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def movsBytes (byte : Bool) : Nat := if byte then 1 else 8

def movsLength (byte : Bool) : Nat := if byte then 2 else 3

def movsCode (byte : Bool) (rex : UInt8) : List UInt8 :=
  if byte then [0xf3, 0xa4] else [0xf3, rex, 0xa5]

theorem movsCode_length (byte : Bool) (rex : UInt8) :
    (movsCode byte rex).length = movsLength byte := by cases byte <;> rfl

theorem movsCode_ne_nil (byte : Bool) (rex : UInt8) :
    movsCode byte rex ≠ [] := by cases byte <;> simp [movsCode]

def repMovsAfter (byte : Bool) (s : RamState) : RamState :=
  afterStep s (movsLength byte) fun t => repCount (movsSpec (8 * movsBytes byte)
    { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte)) })

def repMovsZeroAfter (byte : Bool) (s : RamState) : RamState :=
  afterStep s (movsLength byte) fun t =>
    { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte)), Repeat_String_Operation := false }

theorem repMovsAfter_external (byte : Bool) (s : RamState) :
    (repMovsAfter byte s).external =
      memStore s.external (rdi.read s) ((Operand.mem (rsi.read s) : Operand (8 * movsBytes byte)).read s) := by
  cases byte <;> rfl

theorem repMovsAfter_rflags (byte : Bool) (s : RamState) : (repMovsAfter byte s).RFLAGS = s.RFLAGS := by
  cases byte <;> rfl

theorem repMovsAfter_gpr (byte : Bool) (s : RamState) :
    (repMovsAfter byte s).GPR = Vector.set (Vector.set (Vector.set s.GPR 6 (BitVec.add s.GPR[6] (BitVec.ofNat 64 (movsBytes byte)))) 7
      (BitVec.add s.GPR[7] (BitVec.ofNat 64 (movsBytes byte)))) 1 (s.GPR[1] - 1) := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp only [repMovsAfter, afterStep, finishStep, repCount, Operand.write, movsSpec,
      dataAccess, afterFetches, beforeFetch, resetStepFields, BitVec.ofNat_eq_ofNat,
      Int.reduceToNat, movsLength, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceMul, BitVec.add_eq, Operand.read, gprIndex, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk, Fin.getElem_fin, Fin.isValue,
      BitVec.setWidth_eq, movsBytes, ↓dreduceIte, Nat.reduceDiv, Nat.mul_one,
      Nat.zero_lt_succ, Nat.div_self, mergeGPR_64, Vector.getElem_set, Nat.one_mod,
      Fin.mk_one, Fin.val_one, Bool.not_false, Bool.not_not, Bool.true_and,
      Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    rfl

theorem repMovsAfter_rsi (byte : Bool) (s : RamState) : rsi.read (repMovsAfter byte s) = rsi.read s + BitVec.ofNat 64 (movsBytes byte) := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp only [Operand.read, Int.reduceToNat, repMovsAfter_gpr, movsBytes, Bool.false_eq_true, ↓reduceIte,
      BitVec.add_eq, BitVec.ofNat_eq_ofNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Vector.getElem_set, BitVec.setWidth_eq]
    rfl

theorem repMovsAfter_rdi (byte : Bool) (s : RamState) : rdi.read (repMovsAfter byte s) = rdi.read s + BitVec.ofNat 64 (movsBytes byte) := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp only [Operand.read, Int.reduceToNat, repMovsAfter_gpr, movsBytes, Bool.false_eq_true, ↓reduceIte,
      BitVec.add_eq, BitVec.ofNat_eq_ofNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Vector.getElem_set, BitVec.setWidth_eq]
    rfl

theorem repMovsAfter_rcx (byte : Bool) (s : RamState) : rcx.read (repMovsAfter byte s) = rcx.read s - 1 := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp [Operand.read, repMovsAfter_gpr, movsBytes, gprIndex]

theorem repMovsAfter_repeat (byte : Bool) (s : RamState) :
    (repMovsAfter byte s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp only [repMovsAfter, movsBytes, movsLength, afterStep, finishStep, repCount, rcx_read_movsSpec]
    rfl

theorem repMovsAfter_rip (byte : Bool) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsAfter byte s).RIP = if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte)) else s.RIP := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp only [repMovsAfter, movsBytes, movsLength, afterStep, finishStep, repCount, rcx_read_movsSpec]
    simp [movsSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem AgreesExcept.repMovs (byte : Bool) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (movsBytes byte), .rip] (clearRep s)
      (clearRep (repMovsAfter byte s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repMovsAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6,
        Ne.symm h7]
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [clearRep_external]
    rw [repMovsAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) (movsBytes byte)) (by simp) ⟨i, by omega, he.symm⟩
  · simp only [fixedPart, clearRep, repMovsAfter, repCount, afterStep, finishStep, movsSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repMovsAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem ReadyMidRep.repMovs {byte : Bool} [Bindings] {s : RamState} (h : ReadyMidRep s)
    (htables : IdentityPageTableMemory (repMovsAfter byte s).external) :
    ReadyMidRep (repMovsAfter byte s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsAfter byte s)).external := by
    rw [clearRep_external]
    exact htables
  have : ReadyToStep (clearRep (repMovsAfter byte s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovs byte s) htab
  exact this

theorem repMovsAfter_copy (byte : Bool) (s : RamState) (i : Nat) (hi : i < movsBytes byte)
    (hsrc : (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome) :
    (repMovsAfter byte s).external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    rw [repMovsAfter_external, memStore_getElem?_self _ _ _ (by decide) i (by omega)]
    simp only [Operand.read]
    rw [storedByte_memLoad _ _ i (by omega), memByte]
    simp only [PhysicalMemory.read]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsrc
    change some ((s.external[rsi.read s + BitVec.ofNat 64 i]?).getD 0) =
      s.external[rsi.read s + BitVec.ofNat 64 i]?
    rw [hb]
    rfl

theorem repMovsZeroAfter_external (byte : Bool) (s : RamState) :
    (repMovsZeroAfter byte s).external = s.external := by
  cases byte <;> rfl

theorem repMovsZeroAfter_rip (byte : Bool) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsZeroAfter byte s).RIP = BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte)) := by
  cases hbyte : byte
  all_goals simp only [hbyte] at *
  all_goals
    simp [repMovsZeroAfter, movsLength, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repMovsZeroAfter_repeat (byte : Bool) (s : RamState) :
    (repMovsZeroAfter byte s).Repeat_String_Operation = false := by
  cases byte <;> rfl

theorem AgreesExcept.repMovsZero (byte : Bool) (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repMovsZeroAfter byte s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [fixedPart, clearRep, repMovsZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

theorem rep_movs_step [inst : Bindings] (byte : Bool) (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (rex : UInt8) (hrex : byte = false → RexWPrefix rex.toBitVec)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (movsCode byte rex))
    (hlow : s.RIP.toNat + movsLength byte ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : (rsi.read s).toNat + movsBytes byte ≤ 2^32) (hdst : (rdi.read s).toNat + movsBytes byte ≤ 2^32)
    (hdstPage : (rdi.read s).toNat % 4096 + movsBytes byte ≤ 4096)
    (hsrcMem : ∀ i, i < movsBytes byte → (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < movsBytes byte → (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repMovsAfter byte s)) := by
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) (movsLength byte + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  cases hb : byte
  all_goals
    first
    | have hdecode := decodeLegacy0_run_of_F3_rex_A5 s h rex (hrex hb)
        (by simpa [hb, movsCode] using hcode)
        (by simpa [hb, movsLength] using hlow)
    | have hdecode := Sha3.Proofs.Movs.decodeLegacy0_run_of_F3_A4 s h
        (by simpa [hb, movsCode] using hcode)
        (by simpa [hb, movsLength] using hlow)
    have hform := rep_movs_form byte hstride t (BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte)))
        (if byte then repContext s.DS else repRexContext s.DS rex.toBitVec) ht hmode (by cases byte <;> rfl) (by cases byte <;> rfl) (by cases byte <;> rfl)
        (by intro he; have hh := repRexContext_rex_w (hrex he) s.DS; simpa [he] using hh)
        (by cases byte <;> rfl) (by cases byte <;> rfl) hcpu.ds hcpu.es hdf hcount hsrc hdst hdstPage hsrcMem hdstMem
    simp only [t, hb, movsLength, Bool.false_eq_true, ↓reduceIte] at hform
    rw [hform] at hdecode
    first
    | exact step_f3_rex_legacy0 s _ h rex 0xA5 [] (hrex hb).rexPrefix
        (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
        (by simpa [hb, movsCode] using hcode) (by simpa [hb, movsLength] using hlow) hdecode
        (hmode.of_cs_lma_eq rfl rfl)
    | exact Sha3.Proofs.Stos.step_f3_legacy0_midRep s _ h 0xA4
        (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
        (by simpa [hb, movsCode] using hcode) (by simpa [hb, movsLength] using hlow) rfl hdecode
        (hmode.of_cs_lma_eq rfl rfl)

theorem rep_movs_step_zero [Bindings] (byte : Bool) (s : RamState) (h : ReadyMidRep s) (rex : UInt8)
    (hrex : byte = false → RexWPrefix rex.toBitVec) (hcode : BytesAt s s.RIP (movsCode byte rex))
    (hlow : s.RIP.toNat + movsLength byte ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repMovsZeroAfter byte s)) := by
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) (movsLength byte + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  cases hb : byte
  all_goals
    first
    | have hdecode := decodeLegacy0_run_of_F3_rex_A5 s h rex (hrex hb)
        (by simpa [hb, movsCode] using hcode)
        (by simpa [hb, movsLength] using hlow)
    | have hdecode := Sha3.Proofs.Movs.decodeLegacy0_run_of_F3_A4 s h
        (by simpa [hb, movsCode] using hcode)
        (by simpa [hb, movsLength] using hlow)
    have hform := rep_movs_form_zero byte t (BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte)))
        (if byte then repContext s.DS else repRexContext s.DS rex.toBitVec) (by cases byte <;> rfl) (by cases byte <;> rfl) (by cases byte <;> rfl)
        (by intro he; have hh := repRexContext_rex_w (hrex he) s.DS; simpa [he] using hh) hcount
    simp only [t, hb, movsLength, Bool.false_eq_true, ↓reduceIte] at hform
    rw [hform] at hdecode
    first
    | exact step_f3_rex_legacy0 s _ h rex 0xA5 [] (hrex hb).rexPrefix
        (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
        (by simpa [hb, movsCode] using hcode) (by simpa [hb, movsLength] using hlow) hdecode
        (hmode.of_cs_lma_eq rfl rfl)
    | exact Sha3.Proofs.Stos.step_f3_legacy0_midRep s _ h 0xA4
        (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
        (by simpa [hb, movsCode] using hcode) (by simpa [hb, movsLength] using hlow) rfl hdecode
        (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
