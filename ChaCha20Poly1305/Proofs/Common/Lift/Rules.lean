import ChaCha20Poly1305.Proofs.Common.Lift.Lemma.Lockstep
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Call.Triple

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

section Rules

variable [Bindings] {code : CodeMap} {P : Lifted} {blockCode : CodeMap} {n : Nat}

theorem Rest.ofInside {ρ : RegMap} {e : RamState → Effect} {cs : List Component} {k : Nat}
    {p : BitVec 64} {bytes : List UInt8} {tail : Block Op P.Label signature Reg.count n}
    (h : RestInside code P blockCode ρ e cs [] k p bytes tail) (nonempty : bytes ≠ []) :
    Rest code P blockCode ρ (k + 1) p bytes tail where
  nonempty _ := nonempty
  run regs mem t start hns := h.run regs mem t start (fun _ h => absurd h List.not_mem_nil) hns

theorem RestInside.out {ρ : RegMap} {p : BitVec 64} {ib : List UInt8} {pre : RamState → Prop}
    {e : RamState → Effect} {R : List Reg} {F : List StatusFlag} {cs : List Component}
    {outs : List (EffectPart × Nat)} {k : Nat} {bytes : List UInt8}
    (spec : InstrSpec p ib pre e R F cs) (o : EffectPart) (valid : EffectPart.Valid e cs o)
    (hsets : o.isFlag = true → R.any Reg.isFlag = false → ∀ s, (e s).flags.isSome = true)
    {args : Vector (Fin n) (o.reads R F).length} (hargs : operandsOk ρ (o.reads R F) args = true)
    {tail : Block Op P.Label signature Reg.count (n + 1)}
    (rest : RestInside code P blockCode ρ e cs (outs ++ [(o, n)]) k p bytes tail) :
    RestInside code P blockCode ρ e cs outs k p bytes
      (.letOp (.out p e (o.reads R F) o) args tail) :=
  RestInside.push valid (fun regs mem t start => by
    rw [dialect_eval, start.store]
    simp only [Op.eval, state_operands hargs start.related p,
      EffectPart.value_congr spec.isLocal spec.reads spec.closed spec.params o hsets t]) rest

theorem RestInside.fresh {ρ : RegMap} {p : BitVec 64} {ib : List UInt8} {pre : RamState → Prop}
    {e : RamState → Effect} {R : List Reg} {F : List StatusFlag} {cs : List Component}
    {outs : List (EffectPart × Nat)} {k : Nat} {bytes : List UInt8}
    (spec : InstrSpec p ib pre e R F cs) (f : StatusFlag) (valid : EffectPart.Valid e cs (.flag f))
    (fresh : FlagFresh F e f)
    (hR : R.any Reg.isFlag = true) {args : Vector (Fin n) (Reg.operands R F).length}
    (hargs : operandsOk ρ (Reg.operands R F) args = true)
    {tail : Block Op P.Label signature Reg.count (n + 1)}
    (rest : RestInside code P blockCode ρ e cs (outs ++ [(.flag f, n)]) k p bytes tail) :
    RestInside code P blockCode ρ e cs outs k p bytes
      (.letOp (.out p e (Reg.operands R F) (.flag f)) args tail) :=
  RestInside.push valid (fun regs mem t start => by
    rw [dialect_eval, start.store]
    simp only [Op.eval, state_operands hargs start.related p,
      EffectPart.value_fresh spec.reads spec.closed spec.params hR fresh t]) rest

theorem RestInside.exec {ρ ρ' : RegMap} {p p' : BitVec 64} {ib bytes : List UInt8}
    {pre : RamState → Prop} {e : RamState → Effect} {R : List Reg} {F : List StatusFlag}
    {cs : List Component} {outs : List (EffectPart × Nat)} {k : Nat}
    (spec : InstrSpec p ib pre e R F cs)
    (hrip : ∀ s, pre s → (e s).rip = p') (next : bytes = [] ∨ p + BitVec.ofNat 64 ib.length = p')
    {args : Vector (Fin n) (Reg.operands R F).length}
    (hargs : operandsOk ρ (Reg.operands R F) args = true) (remap : remapOk ρ outs cs ρ' = true)
    {tail : Block Op P.Label signature Reg.count (n + 1)}
    (rest : Rest code P blockCode ρ' k p' bytes tail) :
    RestInside code P blockCode ρ e cs outs k p (ib ++ bytes)
      (.letOp (.exec p pre e (Reg.operands R F)) args tail) where
  run regs mem t start houts hns := by
    have hcodes := start.bytesIn
    rw [codeRange_append] at hcodes
    have hib : ∀ x ∈ codeRange p ib, x ∈ blockCode :=
      fun x hx => hcodes x (List.mem_append_left _ hx)
    have hbytes : ∀ x ∈ codeRange p' bytes, x ∈ blockCode := by
      rcases next with rfl | next
      · intro x hx; simp [codeRange_nil] at hx
      · rw [next] at hcodes
        exact fun x hx => hcodes x (List.mem_append_right _ hx)
    cases hex : (Op.exec p pre e (Reg.operands R F)).eval code (regs.select args) mem with
    | none =>
      exact absurd (by simp only [Block.eval, dialect_eval, hex]) hns
    | some vm =>
      obtain ⟨v, mem'⟩ := vm
      have heval : (Block.letOp (.exec p pre e (Reg.operands R F)) args tail :
          Block Op P.Label signature Reg.count n).eval (dialect code) regs mem =
          tail.eval (dialect code) (regs.push v) mem' := by
        simp only [Block.eval, dialect_eval, hex]
      rw [heval] at hns ⊢
      rw [start.store] at hex
      obtain ⟨hpre, m, t', hrun, hready', hholds, hmem, hsse', hcode', hat'⟩ :=
        exec_run spec hargs (remapOk_spec remap) start.rip start.related start.ready start.sse
          start.codeIn (fun x hx => start.blockIn x (hib x hx)) houts hex
      have hrip' : t'.RIP = p' := hholds.rip.trans (hrip t hpre)
      obtain ⟨u, fin⟩ := rest.run _ mem' t' ⟨hrip', hat', hmem, hready', hsse', hcode', hbytes,
        start.blockIn⟩ hns
      obtain ⟨m', hrun', hk⟩ := fin.run
      refine ⟨u, ⟨m + m', (hrun.mono hib).trans (fun _ hm' => ?_) hrun',
        fun h => absurd h (Nat.succ_ne_zero k)⟩, fin.ready, fin.sse, fin.codeIn,
        fin.fixed.trans hholds.agrees.rest, fin.reached⟩
      have hk' : 0 < k := Nat.pos_of_ne_zero fun h => hm' (hk h)
      rw [hrip']
      exact (codeAt_codeRange (List.length_pos_iff.mpr (rest.nonempty hk'))).mono hbytes

theorem RestInside.ret {ρ ρ' : RegMap} {p : BitVec 64} {ib : List UInt8} {pre : RamState → Prop}
    {e : RamState → Effect} {R : List Reg} {F : List StatusFlag} {cs : List Component}
    {outs : List (EffectPart × Nat)} {jt : Nat} (spec : InstrSpec p ib pre e R F cs)
    (htarget : (EffectPart.target, jt) ∈ outs) {args : Vector (Fin n) (Reg.operands R F).length}
    (hargs : operandsOk ρ (Reg.operands R F) args = true) (remap : remapOk ρ outs cs ρ' = true)
    (hlive : maskLe P.retLive ρ'.mask = true) (hjt : jt < n + 1) :
    RestInside code P blockCode ρ e cs outs 0 p ib
      (.letOp (.exec p pre e (Reg.operands R F)) args
        (.terminate (.ret (ρ'.args (n + 1)) (some ⟨jt, hjt⟩)))) where
  run regs mem t start houts hns := by
    have hib : ∀ x ∈ codeRange p ib, x ∈ code := fun x hx => start.blockIn x (start.bytesIn x hx)
    cases hex : (Op.exec p pre e (Reg.operands R F)).eval code (regs.select args) mem with
    | none =>
      exact absurd (by simp only [Block.eval, dialect_eval, hex]) hns
    | some vm =>
      obtain ⟨v, mem'⟩ := vm
      have heval : (Block.letOp (.exec p pre e (Reg.operands R F)) args
          (.terminate (.ret (ρ'.args (n + 1)) (some ⟨jt, hjt⟩))) :
            Block Op P.Label signature Reg.count n).eval (dialect code) regs mem =
          .returned ⟨Values.select (regs.push v) (ρ'.args (n + 1)), some (regs.push v)[jt],
            mem'⟩ := by
        simp only [Block.eval, dialect_eval, hex]
        rfl
      rw [heval]
      rw [start.store] at hex
      obtain ⟨-, m, t', hrun, hready', hholds, hmem, hsse', hcode', hat'⟩ :=
        exec_run spec hargs (remapOk_spec remap) start.rip start.related start.ready start.sse
          start.codeIn hib houts hex
      obtain ⟨-, hjn, hj⟩ := houts _ htarget
      refine ⟨t', ⟨m, hrun.mono start.bytesIn, fun h => absurd h (Nat.succ_ne_zero 0)⟩, hready',
        hsse', hcode', hholds.agrees.rest, ?_, hat'.args hlive, hmem⟩
      simp only [Vector.getElem_push_lt hjn, hj, EffectPart.value, hholds.rip]

theorem Rest.br {ρ : RegMap} {p : BitVec 64} {target : P.Label} [NeZero n]
    (haddr : P.address target = p) (hlive : maskLe (P.live target) ρ.mask = true) :
    Rest code P blockCode ρ 0 p [] (.terminate (.br ⟨target, ρ.args n⟩)) where
  nonempty h := absurd h (Nat.lt_irrefl 0)
  run _ _ t start _ :=
    ⟨t, ⟨0, .refl t, fun _ => rfl⟩, start.ready, start.sse, start.codeIn, rfl,
      start.rip.trans haddr.symm, start.related.args hlive, start.store⟩

theorem Rest.call {ρ : RegMap} {p ret : BitVec 64} {callee cont : P.Label}
    (haddr : P.address callee = p) (hcont : P.address cont = ret)
    (hret : maskLe (P.live cont) P.retLive = true)
    (hlive : maskLe (P.live callee) ρ.mask = true) :
    Rest code P blockCode ρ 0 p []
      (.letOp (.const ⟨64, ret⟩) #v[] (.terminate (.call ⟨callee, ρ.args (n + 1)⟩
        { target := cont, kept := #v[], arity := rfl, guard := some (Fin.last n) }))) where
  nonempty h := absurd h (Nat.lt_irrefl 0)
  run regs mem t start _ := by
    have heval : (Block.letOp (.const ⟨64, ret⟩) #v[] (.terminate (.call ⟨callee, ρ.args (n + 1)⟩
        { target := cont, kept := #v[], arity := rfl, guard := some (Fin.last n) }) :
          Block Op P.Label signature Reg.count (n + 1))).eval (dialect code) regs mem =
        .call ⟨callee, Values.select (regs.push ⟨64, ret⟩) (ρ.args (n + 1)), mem⟩
          ⟨cont, Values.select (regs.push ⟨64, ret⟩) #v[], rfl,
            some (regs.push ⟨64, ret⟩)[n]⟩ := rfl
    rw [heval]
    refine ⟨t, ⟨0, .refl t, fun _ => rfl⟩, start.ready, start.sse, start.codeIn, rfl,
      start.rip.trans haddr.symm, (start.related.push _).args hlive, start.store, rfl, ?_,
      fun i _ => maskLe_spec hret i⟩
    simp only [Vector.getElem_push_eq, hcont]

theorem Rest.jmp {ρ : RegMap} {p : BitVec 64} {ib : List UInt8} {len : Nat} {off : BitVec 64}
    [NeZero n]
    (step : StepEffect (fun s => s.RIP = p) (codeRange p ib) (fun _ => jmpEffect p len off))
    (nonempty : ib ≠ []) {target : P.Label} (haddr : P.address target = branchTarget p len off)
    (hlive : maskLe (P.live target) ρ.mask = true) :
    Rest code P blockCode ρ 1 p ib (.terminate (.br ⟨target, ρ.args n⟩)) where
  nonempty _ := nonempty
  run regs mem t start _ := by
    have hib : ∀ x ∈ codeRange p ib, x ∈ code := fun x hx => start.blockIn x (start.bytesIn x hx)
    obtain ⟨t', hstep, hready', hholds⟩ := step t start.ready (start.codeIn.mono hib) start.rip
    have hnomem : ∀ c ∈ (jmpEffect p len off).components, ∀ x, ¬ c.Covers x := by
      simp [Component.Covers]
    refine ⟨t', ⟨1, Runs.single hstep, id⟩, hready',
      SupportedSSE.of_agreesExcept hholds.agrees start.sse, hholds.agrees.codeIn hnomem start.codeIn,
      hholds.agrees.rest, hholds.rip.trans haddr.symm, fun i hi hl => ?_, ?_⟩
    · exact (start.related.args hlive i hi hl).trans
        (Reg.read_of_agreesExcept hholds.agrees (by simp [Reg.component_ne_rip])).symm
    · show mem = _
      rw [start.store, hholds.agrees.external hnomem]

theorem Rest.jcc {ρ : RegMap} {p : BitVec 64} {ib : List UInt8} {len : Nat} {cc : BitVec 4}
    {off : BitVec 64}
    (step : StepEffect (fun s => s.RIP = p ∧ (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
        (branchTarget p len off).toNat < 2^32)) (codeRange p ib) (jccEffect p len cc off))
    (nonempty : ib ≠ []) (hlow : (branchTarget p len off).toNat < 2^32)
    {cargs : Vector (Fin n) (condReads cc).length} (hc : operandsOk ρ (condReads cc) cargs = true)
    {taken fall : P.Label} (htaken : P.address taken = branchTarget p len off)
    (hfall : P.address fall = p + BitVec.ofNat 64 len)
    (htlive : maskLe (P.live taken) ρ.mask = true) (hflive : maskLe (P.live fall) ρ.mask = true) :
    Rest code P blockCode ρ 1 p ib
      (.letOp (.pure (condOp cc)) cargs
        (.terminate (.condBr (Fin.last n) ⟨taken, ρ.args (n + 1)⟩ ⟨fall, ρ.args (n + 1)⟩))) where
  nonempty _ := nonempty
  run regs mem t start _ := by
    have hib : ∀ x ∈ codeRange p ib, x ∈ code := fun x hx => start.blockIn x (start.bytesIn x hx)
    obtain ⟨t', hstep, hready', hholds⟩ :=
      step t start.ready (start.codeIn.mono hib) ⟨start.rip, fun _ => hlow⟩
    have hcond := condOp_operands hc start.related
    have hnomem : ∀ c ∈ (jccEffect p len cc off t).components, ∀ x, ¬ c.Covers x := by
      simp [jccEffect, Component.Covers]
    have hat := start.related.push (condOp cc (regs.select cargs))
    have hkeep : ∀ i, (Reg.ofIndex i).read t = (Reg.ofIndex i).read t' := fun i =>
      (Reg.read_of_agreesExcept hholds.agrees (by simp [jccEffect, Reg.component_ne_rip])).symm
    have htruth : (dialect code).truth (regs.push (condOp cc (regs.select cargs)))[Fin.last n] =
        condHolds cc (StatusFlags.ofRFLAGS t.RFLAGS) := by
      show Value.truth _ = _
      rw [show (regs.push (condOp cc (regs.select cargs)))[Fin.last n] =
        condOp cc (regs.select cargs) from Vector.getElem_push_eq]
      exact hcond
    have heval : (Block.letOp (.pure (condOp cc)) cargs
        (.terminate (.condBr (Fin.last n) ⟨taken, ρ.args (n + 1)⟩ ⟨fall, ρ.args (n + 1)⟩)) :
          Block Op P.Label signature Reg.count n).eval (dialect code) regs mem =
        if (dialect code).truth (regs.push (condOp cc (regs.select cargs)))[Fin.last n] then
          .jump ⟨taken, Values.select (regs.push (condOp cc (regs.select cargs)))
            (ρ.args (n + 1)), mem⟩
        else
          .jump ⟨fall, Values.select (regs.push (condOp cc (regs.select cargs)))
            (ρ.args (n + 1)), mem⟩ :=
      rfl
    rw [htruth] at heval
    rw [heval]
    have hmem : mem = t'.external := by rw [start.store, hholds.agrees.external hnomem]
    have hrip := hholds.rip
    simp only [jccEffect, branchEffect] at hrip
    refine ⟨t', ⟨1, Runs.single hstep, id⟩, hready',
      SupportedSSE.of_agreesExcept hholds.agrees start.sse, hholds.agrees.codeIn hnomem start.codeIn,
      hholds.agrees.rest, ?_⟩
    split
    · rename_i hc'
      simp only [hc', ↓reduceIte] at hrip
      exact ⟨hrip.trans htaken.symm, fun i hi hl => (hat.args htlive i hi hl).trans (hkeep i),
        hmem⟩
    · rename_i hc'
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at hrip
      exact ⟨hrip.trans hfall.symm, fun i hi hl => (hat.args hflive i hi hl).trans (hkeep i),
        hmem⟩

theorem Rest.cut {ρ : RegMap} {p : BitVec 64} {ib : List UInt8} :
    Rest code P blockCode ρ 0 p ib (cutBlock p : Block Op P.Label signature Reg.count n) where
  nonempty h := absurd h (Nat.lt_irrefl 0)
  run _ _ _ _ hns := absurd rfl hns

end Rules

end ChaCha20Poly1305.Proofs.Lift
