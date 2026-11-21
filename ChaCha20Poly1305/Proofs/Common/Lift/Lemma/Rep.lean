import ChaCha20Poly1305.Proofs.Common.Lift.Lemma.Eval
import X86Proofs.Instructions.Movs.RepTriple
import X86Proofs.Instructions.Movs.Generated.Rep.Triple
import X86Proofs.Instructions.Stos.Generated.Rep.Triple

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

section Reads

variable {p : BitVec 64} {s t : RamState}

theorem repMovsbEffect_congr (h6 : rsi.read t = rsi.read s) (h7 : rdi.read t = rdi.read s)
    (h1 : rcx.read t = rcx.read s)
    (hm : ∀ a n, (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s) :
    repMovsbEffect p t = repMovsbEffect p s := by
  unfold repMovsbEffect
  rw [h1, h6, h7, hm]

theorem repMovsqEffect_congr (h6 : rsi.read t = rsi.read s) (h7 : rdi.read t = rdi.read s)
    (h1 : rcx.read t = rcx.read s)
    (hm : ∀ a n, (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s) :
    repMovsqEffect p t = repMovsqEffect p s := by
  unfold repMovsqEffect
  rw [h1, h6, h7, hm]

theorem repStosbEffect_congr (h0 : (Operand.reg 0 : Operand 8).read t = (Operand.reg 0).read s)
    (h7 : rdi.read t = rdi.read s) (h1 : rcx.read t = rcx.read s) :
    repStosbEffect p t = repStosbEffect p s := by
  unfold repStosbEffect
  rw [h1, h7, h0]

theorem repStosqEffect_congr (h0 : (Operand.reg 0 : Operand 64).read t = (Operand.reg 0).read s)
    (h7 : rdi.read t = rdi.read s) (h1 : rcx.read t = rcx.read s) :
    repStosqEffect p t = repStosqEffect p s := by
  unfold repStosqEffect
  rw [h1, h7, h0]

end Reads

theorem repMovsbEffect_reads (p : BitVec 64) :
    ReadsOnly p (repMovsbEffect p) [.gpr 6, .gpr 7, .gpr 1, .df] := fun s =>
  (repMovsbEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp)) fun a _ => read_mem_stateOf s a).symm

theorem repMovsqEffect_reads (p : BitVec 64) :
    ReadsOnly p (repMovsqEffect p) [.gpr 6, .gpr 7, .gpr 1, .df] := fun s =>
  (repMovsqEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp)) fun a _ => read_mem_stateOf s a).symm

theorem repStosbEffect_reads (p : BitVec 64) :
    ReadsOnly p (repStosbEffect p) [.gpr 0, .gpr 7, .gpr 1, .df] := fun s =>
  (repStosbEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp))).symm

theorem repStosqEffect_reads (p : BitVec 64) :
    ReadsOnly p (repStosqEffect p) [.gpr 0, .gpr 7, .gpr 1, .df] := fun s =>
  (repStosqEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp))).symm

theorem repMovsbEffect_local {p : BitVec 64} : Effect.Local (repMovsbEffect p) :=
  .of_congr (fun _ _ h => repMovsbEffect_congr (h.read_reg 6) (h.read_reg 7) (h.read_reg 1)
    fun a _ => h.read_mem a) (fun _ => rfl) fun _ w hw => by
    simp only [repMovsbEffect, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> first | rfl | exact mul_mod_eight _ rfl

theorem repStosbEffect_local {p : BitVec 64} : Effect.Local (repStosbEffect p) :=
  .of_congr (fun _ _ h => repStosbEffect_congr (h.read_reg 0) (h.read_reg 7) (h.read_reg 1))
    (fun _ => rfl) fun _ w hw => by
    simp only [repStosbEffect, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> first | rfl | exact mul_mod_eight _ rfl

theorem repStosqEffect_local {p : BitVec 64} : Effect.Local (repStosqEffect p) :=
  .of_congr (fun _ _ h => repStosqEffect_congr (h.read_reg 0) (h.read_reg 7) (h.read_reg 1))
    (fun _ => rfl) fun _ w hw => by
    simp only [repStosqEffect, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> first | rfl | exact mul_mod_eight _ rfl

section Zero

variable [Bindings] {p : BitVec 64}

theorem rep_zero {e : Effect} {s s' : RamState} (h : ReadyToStep s)
    (hstep : X86.Machine.step s = some (.next s')) (hag : AgreesExcept [.rip] s s')
    (hext : s'.external = s.external) (hrip : s'.RIP = e.rip) (hflags : e.flags = none)
    (hwrites : Write.AllHold s' e.writes) :
    ∃ s', X86.Machine.step s = some (.next s') ∧ ReadyToStep s' ∧ e.Holds s s' :=
  ⟨s', hstep, ReadyToStep.of_agreesExcept h hag (hext ▸ h.memory.tables), hrip, hwrites,
    by simp only [Effect.FlagsHold, hflags], hag.mono (by simp [Effect.components])⟩

theorem rep_movsb_zero :
    StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p [0xF3, 0xA4])
      (repMovsbEffect p) := by
  rintro s h hcode ⟨rfl, hz⟩
  have hn : (rcx.read s).toNat = 0 := by rw [hz]; rfl
  have hag := (AgreesExcept.repZero 2 s).of_clearRep h.ready.repeatClear (repZeroAfter_repeat 2 s)
  refine rep_zero (s' := repZeroAfter 2 s) h (rep_movsb_step_zero s h.midRep [0xF3]
    (by simpa using scanPrefix_f3) (by simp) rfl rfl rfl rfl hcode.bytesAt
    (hcode.low (by simp) (by simp)) hz) hag rfl
    (by rw [repZeroAfter_rip _ s h.ready.msr]; rfl) rfl
    ⟨?_, ?_, ?_, BitVec.eq_of_getLsbD_eq fun i (hi : i < 8 * _) => absurd hi (by omega)⟩
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hz]

theorem rep_movsq_zero {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p [0xF3, rex, 0xA5])
      (repMovsqEffect p) := by
  rintro s h hcode ⟨rfl, hz⟩
  have hn : (rcx.read s).toNat = 0 := by rw [hz]; rfl
  have hag := (AgreesExcept.repMovsqZero s).of_clearRep h.ready.repeatClear
    (repMovsqZeroAfter_repeat s)
  refine rep_zero h (rep_movsq_step_zero s h.midRep rex hrex hcode.bytesAt
    (hcode.low (by simp) (by simp)) hz) hag rfl
    (by rw [repMovsqZeroAfter_rip s h.ready.msr]; rfl) rfl
    ⟨?_, ?_, ?_, BitVec.eq_of_getLsbD_eq fun i (hi : i < 64 * _) => absurd hi (by omega)⟩
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hz]

theorem rep_stosb_zero :
    StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p [0xF3, 0xAA])
      (repStosbEffect p) := by
  rintro s h hcode ⟨rfl, hz⟩
  have hn : (rcx.read s).toNat = 0 := by rw [hz]; rfl
  have hag := (AgreesExcept.repZero 2 s).of_clearRep h.ready.repeatClear (repZeroAfter_repeat 2 s)
  refine rep_zero (s' := repZeroAfter 2 s) h (rep_stosb_step_zero s h.midRep [0xF3]
    (by simpa using scanPrefix_f3) (by simp) rfl rfl rfl rfl hcode.bytesAt
    (hcode.low (by simp) (by simp)) hz) hag rfl
    (by rw [repZeroAfter_rip _ s h.ready.msr]; rfl) rfl
    ⟨?_, ?_, BitVec.eq_of_getLsbD_eq fun i (hi : i < 8 * _) => absurd hi (by omega)⟩
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hz]

theorem rep_stosq_zero {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p [0xF3, rex, 0xAB])
      (repStosqEffect p) := by
  rintro s h hcode ⟨rfl, hz⟩
  have hr := hrex.rexPrefix
  have hn : (rcx.read s).toNat = 0 := by rw [hz]; rfl
  have hag := (AgreesExcept.repZero 3 s).of_clearRep h.ready.repeatClear (repZeroAfter_repeat 3 s)
  refine rep_zero (s' := repZeroAfter 3 s) h (rep_stosq_step_zero s h.midRep [0xF3, rex]
    (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp) (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) hcode.bytesAt (hcode.low (by simp) (by simp)) hz)
    hag rfl (by rw [repZeroAfter_rip _ s h.ready.msr]; rfl) rfl
    ⟨?_, ?_, BitVec.eq_of_getLsbD_eq fun i (hi : i < 64 * _) => absurd hi (by omega)⟩
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hz]

end Zero

section Loops

variable [Bindings] {s : RamState} {c : Nat}

theorem RepMovsbLoop.rip_next (h : RepMovsbLoop s (c + 2)) : (repMovsAfter 8 2 s).RIP = s.RIP := by
  have := h.dstLow
  rw [repMovsAfter_rip 8 2 s h.ready.msr, h.counter]
  simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := c + 1) (by omega) (by omega), ↓reduceIte]

theorem ReadyRepLoop.rip_next {rex : UInt8} (h : ReadyRepLoop rex s (c + 2)) :
    (repMovsqAfter s).RIP = s.RIP := by
  have := h.dstLow
  rw [repMovsqAfter_rip s h.ready.msr, h.counter]
  simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := c + 1) (by omega) (by omega), ↓reduceIte]

theorem RepStosbLoop.rip_next (h : RepStosbLoop s (c + 2)) : (repStosAfter 8 2 s).RIP = s.RIP := by
  have := h.dstLow
  rw [repStosAfter_rip 8 2 s h.ready.msr, h.counter]
  simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := c + 1) (by omega) (by omega), ↓reduceIte]

theorem RepStosqLoop.rip_next {rex : UInt8} (h : RepStosqLoop rex s (c + 2)) :
    (repStosAfter 64 3 s).RIP = s.RIP := by
  have := h.dstLow
  rw [repStosAfter_rip 64 3 s h.ready.msr, h.counter]
  simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := c + 1) (by omega) (by omega), ↓reduceIte]

end Loops

section Guards

variable {code : CodeMap} {p : BitVec 64} {t : RamState} {mem : Ram} {pre : RamState → Prop}
  {e : RamState → Effect} {size codeLen : Nat}

theorem RepMovsOk.guard_iff
    (hpre : ∀ t, pre t ↔ t.RIP = p ∧ RepMovsOk [] t.external ((Operand.df : Operand 1).read t)
      (rsi.read t) (rdi.read t) (rcx.read t) size p codeLen)
    (hmem : (e t).components.filter Component.isMem =
      [.mem (rdi.read t) (size * (rcx.read t).toNat)])
    (hrip : t.RIP = p) (hext : t.external = mem) :
    Guard code (RepPre p pre) e t mem ↔
      rcx.read t = 0 ∨ RepMovsOk code mem ((Operand.df : Operand 1).read t) (rsi.read t)
        (rdi.read t) (rcx.read t) size p codeLen := by
  subst hext
  simp only [Guard, avoids_iff_of_mem hmem, writesPresent_iff_of_mem hmem, RepPre, hpre]
  constructor
  · rintro ⟨⟨-, hz⟩ | ⟨-, h⟩, hav, -⟩
    · exact .inl hz
    · exact .inr { h with notCode := hav }
  · rintro (hz | h)
    · refine ⟨.inl ⟨hrip, hz⟩, ?_, ?_⟩ <;> simp [hz]
    · exact ⟨.inr ⟨hrip, { h with notCode := nofun }⟩, h.notCode, h.dstMem⟩

theorem RepStosOk.guard_iff
    (hpre : ∀ t, pre t ↔ t.RIP = p ∧ RepStosOk [] t.external ((Operand.df : Operand 1).read t)
      (rdi.read t) (rcx.read t) size p codeLen)
    (hmem : (e t).components.filter Component.isMem =
      [.mem (rdi.read t) (size * (rcx.read t).toNat)])
    (hrip : t.RIP = p) (hext : t.external = mem) :
    Guard code (RepPre p pre) e t mem ↔
      rcx.read t = 0 ∨ RepStosOk code mem ((Operand.df : Operand 1).read t) (rdi.read t)
        (rcx.read t) size p codeLen := by
  subst hext
  simp only [Guard, avoids_iff_of_mem hmem, writesPresent_iff_of_mem hmem, RepPre, hpre]
  constructor
  · rintro ⟨⟨-, hz⟩ | ⟨-, h⟩, hav, -⟩
    · exact .inl hz
    · exact .inr { h with notCode := hav }
  · rintro (hz | h)
    · refine ⟨.inl ⟨hrip, hz⟩, ?_, ?_⟩ <;> simp [hz]
    · exact ⟨.inr ⟨hrip, { h with notCode := nofun }⟩, h.notCode, h.dstMem⟩

theorem repMovsbEffect_external (t : RamState) :
    (applyWrites t (repMovsbEffect p t).writes).external =
      memStore t.external (rdi.read t)
        (memLoad t.external (rsi.read t) (8 * (rcx.read t).toNat)) :=
  rfl

theorem repMovsqEffect_external (t : RamState) :
    (applyWrites t (repMovsqEffect p t).writes).external =
      memStore t.external (rdi.read t)
        (memLoad t.external (rsi.read t) (64 * (rcx.read t).toNat)) :=
  rfl

theorem repStosbEffect_external (t : RamState) :
    (applyWrites t (repStosbEffect p t).writes).external =
      memStore t.external (rdi.read t)
        (((Operand.reg 0 : Operand 8).read t).replicate (rcx.read t).toNat) :=
  rfl

theorem repStosqEffect_external (t : RamState) :
    (applyWrites t (repStosqEffect p t).writes).external =
      memStore t.external (rdi.read t)
        (((Operand.reg 0 : Operand 64).read t).replicate (rcx.read t).toNat) :=
  rfl

end Guards

end ChaCha20Poly1305.Proofs.Lift
