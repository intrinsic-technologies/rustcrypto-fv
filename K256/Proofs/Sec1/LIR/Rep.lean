import K256.Proofs.Common.Lift.Rep
import X86Proofs.Instructions.Stos.Generated.Rep.Triple

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

section Reads

variable {p : BitVec 64} {s t : RamState}

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

theorem repStosbEffect_reads (p : BitVec 64) :
    ReadsOnly p (repStosbEffect p) [.gpr 0, .gpr 7, .gpr 1, .df] := fun s =>
  (repStosbEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp))).symm

theorem repStosqEffect_reads (p : BitVec 64) :
    ReadsOnly p (repStosqEffect p) [.gpr 0, .gpr 7, .gpr 1, .df] := fun s =>
  (repStosqEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp))).symm

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

section Runs

variable [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64)
include hstride

theorem rep_stosb_runs :
    RunsEffect (RepPre p (RepStosbPre p)) (codeRange p [0xF3, 0xAA]) (repStosbEffect p) :=
  .of_rep (inv := fun c s => RepStosbLoop s c) rep_stosb_zero (rep_stosb_steps hstride p)
    (fun _ h => h.rip)
    (fun _ h hcode hpre hc => ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
      hpre.rip ▸ hcode.low (by simp) (by simp), hc, hpre.dstLow, hpre.dstMem,
      hpre.dstTables, hpre.rip ▸ hpre.dstCode⟩)
    (fun c _ h => h.step hstride c.succ_pos) (fun _ _ h => h.next)
    (fun _ _ h => RepStosbLoop.rip_next h) (by decide)

theorem rep_stosq_runs (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    RunsEffect (RepPre p (RepStosqPre p)) (codeRange p [0xF3, rex, 0xAB]) (repStosqEffect p) :=
  .of_rep (inv := fun c s => RepStosqLoop rex s c) (rep_stosq_zero hrex)
    (rep_stosq_steps hstride p rex hrex) (fun _ h => h.rip)
    (fun _ h hcode hpre hc => ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
      hpre.rip ▸ hcode.low (by simp) (by simp), hc, hpre.dstLow, hpre.dstMem,
      hpre.dstTables, hpre.rip ▸ hpre.dstCode⟩)
    (fun c _ h => h.step hstride hrex c.succ_pos) (fun _ _ h => h.next)
    (fun _ _ h => RepStosqLoop.rip_next h) (by simp)

end Runs

section StateOf

variable {p : BitVec 64} {L : List Reg} {pre : RamState → Prop} {size codeLen : Nat}

theorem RepStosOk.of_stateOf
    (hpre : ∀ t, pre t ↔ t.RIP = p ∧ RepStosOk [] t.external ((Operand.df : Operand 1).read t)
      (rdi.read t) (rcx.read t) size p codeLen)
    (hdi : ∀ s, rdi.read (stateOf p (entriesOf L s) s.external) = rdi.read s)
    (hci : ∀ s, rcx.read (stateOf p (entriesOf L s) s.external) = rcx.read s)
    (hdf : ∀ s, (Operand.df : Operand 1).read (stateOf p (entriesOf L s) s.external) =
      (Operand.df : Operand 1).read s) :
    ∀ s : RamState, s.RIP = p → RepPre p pre (stateOf p (entriesOf L s) s.external) →
      RepPre p pre s :=
  RepPre.of_stateOf hci fun s hrip h => (hpre s).2
    ⟨hrip, by simpa only [hdi, hci, hdf, stateOf_external] using ((hpre _).1 h).2⟩

end StateOf

end K256.Proofs.Sec1.LIR
