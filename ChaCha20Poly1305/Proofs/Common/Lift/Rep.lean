import ChaCha20Poly1305.Proofs.Common.Lift.Footprint
import ChaCha20Poly1305.Proofs.Common.Lift.Eval
import ChaCha20Poly1305.Proofs.Common.Lift.Lemma.Rep

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

def memCopy (mem : Ram) (dst src : BitVec 64) (len : Nat) : Ram :=
  memStore mem dst (memLoad mem src (8 * len))

def memFill {w : Nat} (mem : Ram) (dst : BitVec 64) (v : BitVec w) (count : Nat) : Ram :=
  memStore mem dst (v.replicate count)

section Pre

variable {p : BitVec 64} (t : RamState)

theorem RepMovsbPre.iff : RepMovsbPre p t ↔ t.RIP = p ∧ RepMovsOk [] t.external
    ((Operand.df : Operand 1).read t) (rsi.read t) (rdi.read t) (rcx.read t) 1 p 2 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i, nofun⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, _⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

theorem RepMovsqPre.iff : RepMovsqPre p t ↔ t.RIP = p ∧ RepMovsOk [] t.external
    ((Operand.df : Operand 1).read t) (rsi.read t) (rdi.read t) (rcx.read t) 8 p 3 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i, nofun⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, _⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

theorem RepStosbPre.iff : RepStosbPre p t ↔ t.RIP = p ∧ RepStosOk [] t.external
    ((Operand.df : Operand 1).read t) (rdi.read t) (rcx.read t) 1 p 2 :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f, nofun⟩,
    fun ⟨a, b, c, d, e, f, _⟩ => ⟨a, b, c, d, e, f⟩⟩

theorem RepStosqPre.iff : RepStosqPre p t ↔ t.RIP = p ∧ RepStosOk [] t.external
    ((Operand.df : Operand 1).read t) (rdi.read t) (rcx.read t) 8 p 3 :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f, nofun⟩,
    fun ⟨a, b, c, d, e, f, _⟩ => ⟨a, b, c, d, e, f⟩⟩

end Pre

section Runs

variable [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (p : BitVec 64)
include hstride

theorem rep_movsb_runs :
    RunsEffect (RepPre p (RepMovsbPre p)) (codeRange p [0xF3, 0xA4]) (repMovsbEffect p) :=
  .of_rep (inv := fun c s => RepMovsbLoop s c) rep_movsb_zero (rep_movsb_steps hstride p)
    (fun _ h => h.rip)
    (fun _ h hcode hpre hc => ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
      hpre.rip ▸ hcode.low (by simp) (by simp), hc, hpre.srcLow, hpre.dstLow,
      hpre.srcMem, hpre.dstMem, hpre.disjoint, hpre.dstTables, hpre.rip ▸ hpre.dstCode⟩)
    (fun c _ h => h.step hstride c.succ_pos) (fun _ _ h => h.next)
    (fun _ _ h => RepMovsbLoop.rip_next h) (by decide)

theorem rep_movsq_runs (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) :
    RunsEffect (RepPre p (RepMovsqPre p)) (codeRange p [0xF3, rex, 0xA5]) (repMovsqEffect p) :=
  .of_rep (inv := fun c s => ReadyRepLoop rex s c) (rep_movsq_zero hrex)
    (rep_movsq_steps hstride p rex hrex) (fun _ h => h.rip)
    (fun _ h hcode hpre hc => ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
      hpre.rip ▸ hcode.low (by simp) (by simp), hc, hpre.srcLow, hpre.dstLow,
      hpre.srcMem, hpre.dstMem, hpre.disjoint, hpre.dstTables, hpre.rip ▸ hpre.dstCode⟩)
    (fun c _ h => h.step hstride hrex c.succ_pos) (fun _ _ h => h.next)
    (fun _ _ h => ReadyRepLoop.rip_next h) (by simp)

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

theorem RepPre.of_stateOf (hc : ∀ s, rcx.read (stateOf p (entriesOf L s) s.external) = rcx.read s)
    (hpre : ∀ s, s.RIP = p → pre (stateOf p (entriesOf L s) s.external) → pre s) :
    ∀ s : RamState, s.RIP = p → RepPre p pre (stateOf p (entriesOf L s) s.external) →
      RepPre p pre s :=
  fun s hrip h => h.imp (fun h0 => ⟨hrip, hc s ▸ h0.2⟩) (hpre s hrip)

theorem RepMovsOk.of_stateOf
    (hpre : ∀ t, pre t ↔ t.RIP = p ∧ RepMovsOk [] t.external ((Operand.df : Operand 1).read t)
      (rsi.read t) (rdi.read t) (rcx.read t) size p codeLen)
    (hsi : ∀ s, rsi.read (stateOf p (entriesOf L s) s.external) = rsi.read s)
    (hdi : ∀ s, rdi.read (stateOf p (entriesOf L s) s.external) = rdi.read s)
    (hci : ∀ s, rcx.read (stateOf p (entriesOf L s) s.external) = rcx.read s)
    (hdf : ∀ s, (Operand.df : Operand 1).read (stateOf p (entriesOf L s) s.external) =
      (Operand.df : Operand 1).read s) :
    ∀ s : RamState, s.RIP = p → RepPre p pre (stateOf p (entriesOf L s) s.external) →
      RepPre p pre s :=
  RepPre.of_stateOf hci fun s hrip h => (hpre s).2
    ⟨hrip, by simpa only [hsi, hdi, hci, hdf, stateOf_external] using ((hpre _).1 h).2⟩

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

section Exec

variable (code : CodeMap) (p : BitVec 64) (R : List Reg) (args : Values Value R.length)
  (mem : Ram)

@[cfg_eval ↓] theorem repMovsbEffect_exec :
    Op.eval code (.exec p (RepPre p (RepMovsbPre p)) (repMovsbEffect p) R) args mem =
      if ((Reg.gpr 1).read (Op.state p R args mem)).get 64 = 0 ∨
          RepMovsOk code mem ((Reg.df.read (Op.state p R args mem)).get 1)
            (((Reg.gpr 6).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 1).read (Op.state p R args mem)).get 64) 1 p 2 then
        some (⟨1, 0⟩, memCopy mem (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 6).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 1).read (Op.state p R args mem)).get 64).toNat)
      else none := by
  rw [Op.eval_exec, propext (RepMovsOk.guard_iff RepMovsbPre.iff
      (by rw [repMovsbEffect_components]; rfl) (Op.state_RIP R args) (Op.state_external R args)),
    repMovsbEffect_external, Op.state_external]
  unfold memCopy
  simp only [Operand.read_reg_get, Operand.read_df_get]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[cfg_eval ↓] theorem repMovsqEffect_exec :
    Op.eval code (.exec p (RepPre p (RepMovsqPre p)) (repMovsqEffect p) R) args mem =
      if ((Reg.gpr 1).read (Op.state p R args mem)).get 64 = 0 ∨
          RepMovsOk code mem ((Reg.df.read (Op.state p R args mem)).get 1)
            (((Reg.gpr 6).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 1).read (Op.state p R args mem)).get 64) 8 p 3 then
        some (⟨1, 0⟩, memCopy mem (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 6).read (Op.state p R args mem)).get 64)
          (8 * (((Reg.gpr 1).read (Op.state p R args mem)).get 64).toNat))
      else none := by
  rw [Op.eval_exec, propext (RepMovsOk.guard_iff RepMovsqPre.iff
      (by rw [repMovsqEffect_components]; rfl) (Op.state_RIP R args) (Op.state_external R args)),
    repMovsqEffect_external, Op.state_external]
  unfold memCopy
  rw [show ∀ n, 8 * (8 * n) = 64 * n from fun n => by omega]
  simp only [Operand.read_reg_get, Operand.read_df_get]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[cfg_eval ↓] theorem repStosbEffect_exec :
    Op.eval code (.exec p (RepPre p (RepStosbPre p)) (repStosbEffect p) R) args mem =
      if ((Reg.gpr 1).read (Op.state p R args mem)).get 64 = 0 ∨
          RepStosOk code mem ((Reg.df.read (Op.state p R args mem)).get 1)
            (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 1).read (Op.state p R args mem)).get 64) 1 p 2 then
        some (⟨1, 0⟩, memFill mem (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 0).read (Op.state p R args mem)).get 8)
          (((Reg.gpr 1).read (Op.state p R args mem)).get 64).toNat)
      else none := by
  rw [Op.eval_exec, propext (RepStosOk.guard_iff RepStosbPre.iff
      (by rw [repStosbEffect_components]; rfl) (Op.state_RIP R args) (Op.state_external R args)),
    repStosbEffect_external, Op.state_external]
  unfold memFill
  simp only [Operand.read_reg_get, Operand.read_df_get]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

@[cfg_eval ↓] theorem repStosqEffect_exec :
    Op.eval code (.exec p (RepPre p (RepStosqPre p)) (repStosqEffect p) R) args mem =
      if ((Reg.gpr 1).read (Op.state p R args mem)).get 64 = 0 ∨
          RepStosOk code mem ((Reg.df.read (Op.state p R args mem)).get 1)
            (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
            (((Reg.gpr 1).read (Op.state p R args mem)).get 64) 8 p 3 then
        some (⟨1, 0⟩, memFill mem (((Reg.gpr 7).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 0).read (Op.state p R args mem)).get 64)
          (((Reg.gpr 1).read (Op.state p R args mem)).get 64).toNat)
      else none := by
  rw [Op.eval_exec, propext (RepStosOk.guard_iff RepStosqPre.iff
      (by rw [repStosqEffect_components]; rfl) (Op.state_RIP R args) (Op.state_external R args)),
    repStosqEffect_external, Op.state_external]
  unfold memFill
  simp only [Operand.read_reg_get, Operand.read_df_get]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end Exec

end ChaCha20Poly1305.Proofs.Lift
