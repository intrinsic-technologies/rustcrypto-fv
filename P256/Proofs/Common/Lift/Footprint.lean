import P256.Proofs.Common.Lift.Rules
import P256.Proofs.Common.Lift.Lemma.Read
import X86Proofs.Instructions.Jmp.Generated.R.Triple
import X86Proofs.Instructions.Jmp.Generated.M.Triple

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

structure EffectFootprint (p : BitVec 64) (e : RamState → Effect) (R : List Reg)
    (F : List StatusFlag) (cs : List Component) : Prop where
  isLocal : LocalWith F e
  reads : ReadsOnly p e R
  closed : Reg.FlagsClosed R
  params : ∀ f ∈ F, Reg.flag f ∈ R
  components : ∀ s c, c.isMem = false → (c ∈ (e s).components ↔ c ∈ cs)

theorem EffectFootprint.toInstrSpecOfRuns [Bindings] {p : BitVec 64} {ib : List UInt8}
    {pre : RamState → Prop} {e : RamState → Effect} {R : List Reg} {F : List StatusFlag}
    {cs : List Component}
    (fp : EffectFootprint p e R F cs) (runs : RunsEffect pre (codeRange p ib) e)
    (hpre : ∀ s, s.RIP = p → pre (stateOf p (entriesOf (Reg.operands R F) s) s.external) →
      pre s) :
    InstrSpec p ib pre e R F cs :=
  ⟨runs, fp.isLocal, fp.reads, fp.closed, fp.params, hpre, fp.components⟩

theorem EffectFootprint.toInstrSpec [Bindings] {p : BitVec 64} {ib : List UInt8}
    {pre : RamState → Prop} {e : RamState → Effect} {R : List Reg} {F : List StatusFlag}
    {cs : List Component}
    (fp : EffectFootprint p e R F cs) (step : StepEffect pre (codeRange p ib) e)
    (hpre : ∀ s, s.RIP = p → pre (stateOf p (entriesOf (Reg.operands R F) s) s.external) →
      pre s) :
    InstrSpec p ib pre e R F cs :=
  fp.toInstrSpecOfRuns (StepEffect.runs step) hpre

theorem InstrSpec.goesTo [Bindings] {p : BitVec 64} {ib : List UInt8} {pre : RamState → Prop}
    {e : RamState → Effect} {R : List Reg} {F : List StatusFlag} {cs : List Component}
    (spec : InstrSpec p ib pre e R F cs) (t : BitVec 64) :
    InstrSpec p ib (GoesTo pre e t) e R F cs where
  run s hready hcode h := spec.run s hready hcode h.1
  isLocal := spec.isLocal
  reads := spec.reads
  closed := spec.closed
  params := spec.params
  pre s hrip h := by
    refine ⟨spec.pre s hrip h.1, ?_⟩
    rw [spec.reads s]
    exact (spec.isLocal.rip _ _ (stateOf_obs_of_nonFlags p (nonFlags_operands R F) s)
      (flagsAgree_stateOf p spec.params (fun _ h => mem_operands (R := R) h) s)).trans h.2
  components := spec.components

theorem LocalWith.ofLocal {e : RamState → Effect} {F : List StatusFlag} (h : Effect.Local e) :
    LocalWith F e :=
  ⟨fun t t' ho _ => h.rip t t' ho, fun t t' ho _ => h.writes t t' ho,
    fun t t' ho _ => h.flagsSome t t' ho, fun t t' ho _ => h.flag t t' ho, h.full⟩

theorem LocalWith.atFlags {α : Type} {f : StatusFlags → α} {e : α → RamState → Effect}
    {F : List StatusFlag} (hf : ∀ {a b : StatusFlags}, (∀ x ∈ F, a.get x = b.get x) → f a = f b)
    (hl : ∀ c, Effect.Local (e c)) : LocalWith F (atFlags f e) := by
  have hc : ∀ t t', FlagsAgree F t t' →
      f (StatusFlags.ofRFLAGS t.RFLAGS) = f (StatusFlags.ofRFLAGS t'.RFLAGS) :=
    fun _ _ h => hf h
  refine ⟨fun t t' ho h => ?_, fun t t' ho h => ?_, fun t t' ho h => ?_, fun t t' ho h i hi => ?_,
    fun t => (hl _).full t⟩
  all_goals simp only [_root_.P256.Proofs.Lift.atFlags]; rw [hc t t' h]
  · exact (hl _).rip t t' ho
  · exact (hl _).writes t t' ho
  · exact (hl _).flagsSome t t' ho
  · exact (hl _).flag t t' ho i hi

theorem StepEffect.atFlags [Bindings] {α : Type} {pre : RamState → Prop} {code : CodeMap}
    {f : StatusFlags → α} {e : α → RamState → Effect}
    (h : ∀ c, StepEffect (fun s => pre s ∧ f (StatusFlags.ofRFLAGS s.RFLAGS) = c) code (e c)) :
    StepEffect pre code (_root_.P256.Proofs.Lift.atFlags f e) :=
  fun s hready hcode hpre => h _ s hready hcode ⟨hpre, rfl⟩

instance (rex : BitVec 8) : Decidable (RexPrefix rex) := by unfold RexPrefix; infer_instance
instance (rex : BitVec 8) : Decidable (RexWPrefix rex) := by unfold RexWPrefix; infer_instance
instance (rex : BitVec 8) : Decidable (RexNoWPrefix rex) := by unfold RexNoWPrefix; infer_instance

theorem pre_rip {p : BitVec 64} {L : List Reg} :
    ∀ s : RamState, s.RIP = p →
      (fun t : RamState => t.RIP = p) (stateOf p (entriesOf L s) s.external) →
        (fun t : RamState => t.RIP = p) s :=
  fun _ h _ => h

theorem StorePre.of_stateOf {p : BitVec 64} {codeLen : Nat} {addr : RamState → BitVec 64}
    {len : Nat} {L : List Reg}
    (haddr : ∀ s, addr (stateOf p (entriesOf L s) s.external) = addr s) :
    ∀ s : RamState, s.RIP = p → StorePre p codeLen addr len
      (stateOf p (entriesOf L s) s.external) → StorePre p codeLen addr len s := by
  intro s hrip h
  obtain ⟨-, hw, hc⟩ := h
  rw [haddr] at hw hc
  exact ⟨hrip, hw.of_external_eq (stateOf_external _ _ _).symm, hc⟩

theorem LoadPre.of_stateOf {p : BitVec 64} {addr : RamState → BitVec 64} {len : Nat}
    {L : List Reg} (haddr : ∀ s, addr (stateOf p (entriesOf L s) s.external) = addr s) :
    ∀ s : RamState, s.RIP = p → LoadPre p addr len
      (stateOf p (entriesOf L s) s.external) → LoadPre p addr len s := by
  intro s hrip h
  obtain ⟨-, hr⟩ := h
  rw [haddr] at hr
  exact ⟨hrip, hr.of_external_eq (stateOf_external _ _ _).symm⟩

theorem LoadPre.of_addr {p q : BitVec 64} {am : AddrMode} {len : Nat} {L : List Reg}
    (h : addrRegsIn am L = true) :
    ∀ s : RamState, s.RIP = p → LoadPre p (fun s => am.addr s q) len
      (stateOf p (entriesOf L s) s.external) →
        LoadPre p (fun s => am.addr s q) len s :=
  LoadPre.of_stateOf fun s => addr_stateOf am s (fun _ => mem_of_addrRegsIn h) q

theorem StorePre.of_addr {p q : BitVec 64} {codeLen : Nat} {am : AddrMode} {len : Nat}
    {L : List Reg} (h : addrRegsIn am L = true) :
    ∀ s : RamState, s.RIP = p → StorePre p codeLen (fun s => am.addr s q) len
      (stateOf p (entriesOf L s) s.external) →
        StorePre p codeLen (fun s => am.addr s q) len s :=
  StorePre.of_stateOf fun s => addr_stateOf am s (fun _ => mem_of_addrRegsIn h) q

theorem RetPre.of_stateOf {p : BitVec 64} {L : List Reg}
    (hsp : ∀ s, stackPtr (stateOf p (entriesOf L s) s.external) = stackPtr s) :
    ∀ s : RamState, s.RIP = p → RetPre p (stateOf p (entriesOf L s) s.external) →
      RetPre p s := by
  intro s hrip ⟨hpop, htop⟩
  refine ⟨LoadPre.of_stateOf hsp s hrip hpop, ?_⟩
  simp only [stackTop, Operand.read_mem_external, stateOf_external, hsp] at htop
  simpa only [stackTop, Operand.read_mem_external] using htop

theorem CallPre.of_stateOf {p : BitVec 64} {len : Nat} {target : RamState → BitVec 64}
    {L : List Reg} (hsp : ∀ s, pushAddr (stateOf p (entriesOf L s) s.external) = pushAddr s)
    (ht : ∀ s, target (stateOf p (entriesOf L s) s.external) = target s) :
    ∀ s : RamState, s.RIP = p → CallPre p len target (stateOf p (entriesOf L s) s.external) →
      CallPre p len target s :=
  fun s hrip h => ⟨StorePre.of_stateOf hsp s hrip h.1, ht s ▸ h.2⟩

theorem CallMemPre.of_addr {p : BitVec 64} {am : AddrMode} {L : List Reg}
    (h : addrRegsIn am L = true)
    (hsp : ∀ s, pushAddr (stateOf p (entriesOf L s) s.external) = pushAddr s) :
    ∀ s : RamState, s.RIP = p → CallMemPre p am (stateOf p (entriesOf L s) s.external) →
      CallMemPre p am s := by
  intro s hrip ⟨⟨hpush, ht⟩, hr⟩
  have ha := addr_stateOf am (p := p) (mem := s.external) s (fun _ => mem_of_addrRegsIn h)
    (p + BitVec.ofNat 64 (callMemLen am))
  simp only [callMemPtr, Operand.read_mem_external, stateOf_external, ha] at ht hr
  exact ⟨⟨StorePre.of_stateOf hsp s hrip hpush, ht⟩,
    hr.of_external_eq (stateOf_external _ _ _).symm⟩

theorem JmpRegPre.of_stateOf {p : BitVec 64} {r : BitVec 5} {L : List Reg}
    (h : ∀ s, (Operand.reg r : Operand 64).read (stateOf p (entriesOf L s) s.external) =
      (Operand.reg r : Operand 64).read s) :
    ∀ s : RamState, s.RIP = p → JmpRegPre p r (stateOf p (entriesOf L s) s.external) →
      JmpRegPre p r s :=
  fun s hrip ht => ⟨hrip, h s ▸ ht.2⟩

theorem JmpMemPre.of_addr {p : BitVec 64} {len : Nat} {am : AddrMode} {L : List Reg}
    (h : addrRegsIn am L = true) :
    ∀ s : RamState, s.RIP = p → JmpMemPre p len am (stateOf p (entriesOf L s) s.external) →
      JmpMemPre p len am s := by
  intro s hrip ⟨hl, ht⟩
  have ha := addr_stateOf am (p := p) (mem := s.external) s (fun _ => mem_of_addrRegsIn h)
    (p + BitVec.ofNat 64 len)
  simp only [jmpM64Effect, Operand.read_mem_external, stateOf_external, ha] at ht
  exact ⟨LoadPre.of_addr h s hrip hl, by simpa only [jmpM64Effect, Operand.read_mem_external]⟩

syntax "lift_reads" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| lift_reads $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      intro s
      simp only [Operand.read_reg_get, Operand.read_df_get, Operand.read_mxcsr_get,
        stackPtr_get, pushAddr, stackTop, ofRFLAGS_eq_regs, Operand.read_mem_external,
        stateOf_external, read_stateOf_entriesOf, addr_stateOf_append,
        addr_stateOf_addrRegs, List.mem_append, List.mem_cons, List.mem_singleton, true_or,
        or_true, Reg.operands, Reg.nonFlags, List.filter_cons, List.filter_nil, List.filter_append,
        List.map_cons, List.map_nil, List.append_nil, Reg.isFlag, Bool.not_false,
        Bool.not_true, ite_true, ite_false, Bool.cond_true, Bool.cond_false, $ls,*]

      try rfl))

macro "lift_components" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro s c hc
  simp only [$ls,*]
  try (cases c <;> simp_all [Component.isMem])))

macro "lift_closed" : tactic =>
  `(tactic| simp [Reg.FlagsClosed, Reg.flags, Reg.isFlag, addrRegs_any_isFlag])

macro "lift_params" : tactic => `(tactic| (
  intro f hf
  cases f <;> simp_all))

macro "lift_fresh" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro f hf t t' h hF
  try simp only [FlagsAgree, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    StatusFlags.get] at hF
  cases f <;> simp_all [$ls,*, Effect.flag, StatusFlagsOutcome.get,
    StatusFlagsOutcome.ofStatusFlags, h.read_reg, h.read_mem, h.read_gpr8, h.read_byteReg,
    AddrMode.addr_obs h]))

end P256.Proofs.Lift
