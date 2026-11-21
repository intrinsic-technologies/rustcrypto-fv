import ChaCha20Poly1305.Proofs.Common.Lift.Rep

namespace ChaCha20Poly1305.Proofs.Decrypt.Movsd

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

section
variable {p : BitVec 64} {s t : RamState}

theorem repMovsdEffect_congr (h6 : rsi.read t = rsi.read s) (h7 : rdi.read t = rdi.read s)
    (h1 : rcx.read t = rcx.read s)
    (hm : ∀ a n, (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s) :
    repMovsdEffect p t = repMovsdEffect p s := by
  unfold repMovsdEffect
  rw [h1, h6, h7, hm]

end

theorem repMovsdEffect_reads (p : BitVec 64) :
    ReadsOnly p (repMovsdEffect p) [.gpr 6, .gpr 7, .gpr 1, .df] := fun s =>
  (repMovsdEffect_congr (read_reg_stateOf s (by simp)) (read_reg_stateOf s (by simp))
    (read_reg_stateOf s (by simp)) fun a _ => read_mem_stateOf s a).symm

theorem repMovsdEffect_local {p : BitVec 64} : Effect.Local (repMovsdEffect p) :=
  .of_congr (fun _ _ h => repMovsdEffect_congr (h.read_reg 6) (h.read_reg 7) (h.read_reg 1)
    fun a _ => h.read_mem a) (fun _ => rfl) fun _ w hw => by
    simp only [repMovsdEffect, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> first | rfl | exact mul_mod_eight _ rfl

section
variable [Bindings] {p : BitVec 64}

theorem rep_movsd_zero :
    StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p [0xF3, 0xA5])
      (repMovsdEffect p) := by
  rintro s h hcode ⟨rfl, hz⟩
  have hn : (rcx.read s).toNat = 0 := by rw [hz]; rfl
  have hag := (AgreesExcept.repZero 2 s).of_clearRep h.ready.repeatClear (repZeroAfter_repeat 2 s)
  refine rep_zero (s' := repZeroAfter 2 s) h (rep_movsd_step_zero s h.midRep [0xF3]
    (by simpa using scanPrefix_f3) (by simp) rfl rfl rfl rfl rfl rfl hcode.bytesAt
    (hcode.low (by simp) (by simp)) hz) hag rfl
    (by rw [repZeroAfter_rip _ s h.ready.msr]; rfl) rfl
    ⟨?_, ?_, ?_, BitVec.eq_of_getLsbD_eq fun i (hi : i < 32 * _) => absurd hi (by omega)⟩
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hn]; simp
  · rw [hag.read (by simp), hz]

end
section
variable [Bindings] {s : RamState} {c : Nat}

theorem RepMovsdLoop.rip_next (h : RepMovsdLoop s (c + 2)) : (repMovsAfter 32 2 s).RIP = s.RIP := by
  have := h.dstLow
  rw [repMovsAfter_rip 32 2 s h.ready.msr, h.counter]
  simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := c + 1) (by omega) (by omega), ↓reduceIte]

end
section
variable {p : BitVec 64}

theorem repMovsdEffect_external (t : RamState) :
    (applyWrites t (repMovsdEffect p t).writes).external =
      memStore t.external (rdi.read t)
        (memLoad t.external (rsi.read t) (32 * (rcx.read t).toNat)) :=
  rfl

theorem RepMovsdPre.iff (t : RamState) : RepMovsdPre p t ↔ t.RIP = p ∧ RepMovsOk [] t.external
    ((Operand.df : Operand 1).read t) (rsi.read t) (rdi.read t) (rcx.read t) 4 p 2 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i, nofun⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, _⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

end
section
variable [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64)
include hstride

theorem rep_movsd_runs :
    RunsEffect (RepPre p (RepMovsdPre p)) (codeRange p [0xF3, 0xA5]) (repMovsdEffect p) :=
  .of_rep (inv := fun c s => RepMovsdLoop s c) rep_movsd_zero (rep_movsd_steps hstride p)
    (fun _ h => h.rip)
    (fun _ h hcode hpre hc => ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
      hpre.rip ▸ hcode.low (by simp) (by simp), hc, hpre.srcLow, hpre.dstLow,
      hpre.srcMem, hpre.dstMem, hpre.disjoint, hpre.dstTables, hpre.rip ▸ hpre.dstCode⟩)
    (fun c _ h => h.step hstride c.succ_pos) (fun _ _ h => h.next)
    (fun _ _ h => RepMovsdLoop.rip_next h) (by decide)

end
section
variable (code : CodeMap) (p : BitVec 64) (R : List Reg) (args : Values Value R.length) (mem : Ram)

@[cfg_eval ↓] theorem repMovsdEffect_exec :
    Op.eval code (.exec p (RepPre p (RepMovsdPre p)) (repMovsdEffect p) R) args mem =
      if ((Reg.gpr 1).read (Op.state p R args mem)).get 64 = 0 ∨
          RepMovsOk code mem ((Reg.df.read (Op.state p R args mem)).get 1)
            (((Reg.gpr 6).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 1).read (Op.state p R args mem)).get 64) 4 p 2 then
        some (⟨1, 0⟩, memCopy mem (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 6).read (Op.state p R args mem)).get 64)
          (4 * (((Reg.gpr 1).read (Op.state p R args mem)).get 64).toNat))
      else none := by
  rw [Op.eval_exec, propext (RepMovsOk.guard_iff RepMovsdPre.iff
      (by rw [repMovsdEffect_components]; rfl) (Op.state_RIP R args) (Op.state_external R args)),
    repMovsdEffect_external, Op.state_external]
  unfold memCopy
  rw [show ∀ n, 8 * (4 * n) = 32 * n from fun n => by omega]
  simp only [Operand.read_reg_get, Operand.read_df_get]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end

theorem repMovsdEffect_footprint (p : BitVec 64) :
    EffectFootprint p (repMovsdEffect p) ([.gpr 6, .gpr 7, .gpr 1, .df]) []
      [.reg 6, .reg 7, .reg 1, .rip] :=
  ⟨.ofLocal repMovsdEffect_local, repMovsdEffect_reads p, by lift_closed, by lift_params,
    by lift_components [repMovsdEffect_components]⟩

@[cfg_eval] theorem_by repMovsdEffect_rsi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 6)).value (repMovsdEffect p t) t' = _ := by lift_value [repMovsdEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsdEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repMovsdEffect p t) t' = _ := by lift_value [repMovsdEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsdEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repMovsdEffect p t) t' = _ := by lift_value [repMovsdEffect, Nat.one_mul]

end ChaCha20Poly1305.Proofs.Decrypt.Movsd
