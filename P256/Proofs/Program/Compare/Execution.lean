import P256.Proofs.Program.Compare.Instructions.Common
import X86Proofs.Program.Execution

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86Proofs

def InRoutine (ip : BitVec 64) : Prop :=
  0x11c860 ≤ ip.toNat ∧ ip.toNat ≤ 0x11ce9e

def RegisterBoundary (boundary : ReturnBoundary) (s : RamState) : Prop :=
  stackPtr s ≠ boundary.rsp ∨ ∀ ip, InRoutine ip → ip ≠ boundary.rip

theorem RegisterBoundary.of_stack_eq {boundary : ReturnBoundary} {s t : RamState}
    (h : RegisterBoundary boundary s) (he : stackPtr t = stackPtr s) :
    RegisterBoundary boundary t := by
  rcases h with h | h
  · exact Or.inl (he ▸ h)
  · exact Or.inr h

theorem RegisterBoundary.advances [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    (h : RegisterBoundary boundary s) (hstep : Machine.step s = some (.next t))
    (hsp : stackPtr t = stackPtr s) (hip : InRoutine t.RIP) : Advances boundary 1 s t := by
  apply Advances.of_step hstep
  rcases h with h | h
  · apply Or.inr
    change stackPtr t ≠ boundary.rsp
    simpa only [hsp] using h
  · exact Or.inl (h _ hip)

theorem holds_after_rip {e : Effect} {s u t : RamState} {ip : BitVec 64}
    (h : e.Holds s u) (ha : AgreesExcept [.rip] u t) (hip : t.RIP = ip)
    (hfull : ∀ w ∈ e.writes, w.Full) :
    ({ e with rip := ip } : Effect).Holds s t := by
  have hr {n : Nat} (op : Operand n) (hf : op.Full) : op.read t = op.read u := by
    cases op with
    | reg r => exact ha.read (by simp)
    | regHigh r => exact ha.read_regHigh (by simp)
    | mxcsr => simp only [Operand.read, ha.mxcsr (by simp)]
    | df => simp only [Operand.read, ha.df (by simp)]
    | fpr r | mmx r => simp only [Operand.read, ha.fpr (r := r) (by simp)]
    | fsw => simp only [Operand.read, ha.fsw (by simp)]
    | fcc m => simp only [Operand.read, ha.fcc (by simp)]
    | ftw => simp only [Operand.read, ha.ftw (by simp)]
    | fcw => simp only [Operand.read, ha.fcw (by simp)]
    | fpuPtr => simp only [Operand.read, ha.fpuPtr (by simp)]
    | mem addr =>
      change memLoad t.external addr n = memLoad u.external addr n
      rw [ha.external (by simp [Component.Covers])]
    | xmm r =>
      change n = 128 at hf
      subst n
      exact ha.read_xmm (by simp)
  refine ⟨hip, ?_, ?_, ?_⟩
  · apply Write.allHold_iff.mpr
    intro w hw
    rw [hr w.dst (hfull w hw)]
    exact Write.allHold_iff.mp h.writes w hw
  · change e.FlagsHold t
    unfold Effect.FlagsHold
    rw [ha.rflags (by simp) (by simp)]
    exact h.flags
  · change AgreesExcept e.components s t
    apply (h.agrees.trans ha).mono
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hc
    · simp [Effect.components]

def RegisterBlock [Bindings] (pre : RamState → Prop) (code : CodeMap)
    (effect : RamState → Effect) : Prop :=
  ∀ (boundary : ReturnBoundary) s, ReadyToStep s → CodeIn code s → pre s →
    RegisterBoundary boundary s →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      (effect s).Holds s t ∧ stackPtr t = stackPtr s

namespace RegisterBlock

variable [Bindings] {P pre₁ pre₂ : RamState → Prop}
  {code code₁ code₂ : CodeMap} {E e₁ e₂ E' : RamState → Effect}

theorem first (hStep : StepEffect pre₁ code₁ e₁)
    (hSub : ∀ x ∈ code₁, x ∈ code) (hPre : ∀ s, P s → pre₁ s)
    (hAvoid : ∀ s, P s → (e₁ s).Avoids code)
    (hStack : ∀ s, P s → .reg 4 ∉ (e₁ s).components)
    (hIP : ∀ s, P s → InRoutine (e₁ s).rip) :
    RegisterBlock P code e₁ := by
  intro boundary s hReady hCode hP hBoundary
  obtain ⟨t, hStep', hReady', hEffect⟩ := hStep s hReady (hCode.mono hSub) (hPre s hP)
  have hsp : stackPtr t = stackPtr s := hEffect.agrees.read (n := 64) (hStack s hP)
  refine ⟨1, t, Advances.of_step hStep' ?_, hReady',
    hEffect.codeIn (hAvoid s hP) hCode, hEffect, hsp⟩
  rcases hBoundary with hBoundary | hBoundary
  · apply Or.inr
    change stackPtr t ≠ boundary.rsp
    simpa only [hsp] using hBoundary
  · exact Or.inl (hEffect.rip ▸ hBoundary _ (hIP s hP))

theorem seq_step (hBlock : RegisterBlock P code E)
    (hStep : StepEffect pre₂ code₂ e₂) (hLocal : Effect.Local e₂)
    (hSub : ∀ x ∈ code₂, x ∈ code)
    (hFull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hMid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code)
    (hStack : ∀ t, pre₂ t → .reg 4 ∉ (e₂ t).components)
    (hIP : ∀ t, pre₂ t → InRoutine (e₂ t).rip) :
    RegisterBlock P code (Effect.seq E e₂) := by
  intro boundary s hReady hCode hP hBoundary
  obtain ⟨fuel, t, hAdvance, hReady', hCode', hEffect, hsp⟩ :=
    hBlock boundary s hReady hCode hP hBoundary
  obtain ⟨hPre, hAvoid⟩ := hMid s t hP hEffect (hEffect.obsAfter (hFull s hP))
  obtain ⟨u, hStep', hReady'', hEffect'⟩ := hStep t hReady' (hCode'.mono hSub) hPre
  have hsp' : stackPtr u = stackPtr t := hEffect'.agrees.read (n := 64) (hStack t hPre)
  refine ⟨fuel + 1, u, hAdvance.trans (Advances.of_step hStep' ?_), hReady'',
    hEffect'.codeIn hAvoid hCode', hEffect.seq hLocal (hFull s hP) hEffect', hsp'.trans hsp⟩
  rcases hBoundary with hBoundary | hBoundary
  · apply Or.inr
    change stackPtr u ≠ boundary.rsp
    simpa only [hsp', hsp] using hBoundary
  · exact Or.inl (hEffect'.rip ▸ hBoundary _ (hIP t hPre))

theorem block_first
    (k : RegisterBlock P code e₁ → RegisterBlock P code E')
    (hStep : StepEffect pre₁ code₁ e₁) (hSub : ∀ x ∈ code₁, x ∈ code)
    (hPre : ∀ s, P s → pre₁ s) (hAvoid : ∀ s, P s → (e₁ s).Avoids code)
    (hStack : ∀ s, P s → .reg 4 ∉ (e₁ s).components)
    (hIP : ∀ s, P s → InRoutine (e₁ s).rip) :
    RegisterBlock P code E' :=
  k (first hStep hSub hPre hAvoid hStack hIP)

theorem block_then
    (k : RegisterBlock P code (Effect.seq E e₂) → RegisterBlock P code E')
    (hStep : StepEffect pre₂ code₂ e₂) (hLocal : Effect.Local e₂)
    (hSub : ∀ x ∈ code₂, x ∈ code)
    (hFull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hMid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code)
    (hStack : ∀ t, pre₂ t → .reg 4 ∉ (e₂ t).components)
    (hIP : ∀ t, pre₂ t → InRoutine (e₂ t).rip) :
    RegisterBlock P code E → RegisterBlock P code E' :=
  fun hBlock ↦ k (hBlock.seq_step hStep hLocal hSub hFull hMid hStack hIP)

theorem block_end (hEffect : ∀ s t, P s → (E s).Holds s t → (E' s).Holds s t) :
    RegisterBlock P code E → RegisterBlock P code E' := by
  intro hBlock boundary s hReady hCode hP hBoundary
  obtain ⟨fuel, t, hAdvance, hReady', hCode', hOld, hsp⟩ :=
    hBlock boundary s hReady hCode hP hBoundary
  exact ⟨fuel, t, hAdvance, hReady', hCode', hEffect s t hP hOld, hsp⟩

end RegisterBlock

macro "p256_memcmp_run_begin " t:term : tactic => `(tactic| (
  refine RegisterBlock.block_first ?k $t ?sub ?pre ?av ?stack ?ip
  try (case sub => x86_sub)
  try (case pre => intro s hP; first
    | exact hP.rip | exact ⟨hP.rip⟩ | exact hP | exact hP.1
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
       x86_norm; x86_frame))
  try (case av => intro _ _; x86_avoid)
  try (case stack => intro _ _; x86_norm)
  try (case ip => intro _ _; constructor <;> x86_norm <;> decide +kernel)
  case' k => x86_norm))

macro "p256_memcmp_run_then " t:term : tactic => `(tactic| (
  refine RegisterBlock.block_then ?k $t ?loc ?sub ?full ?mid ?stack ?ip
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case mid => x86_mid)
  try (case stack => intro _ _; x86_norm)
  try (case ip => intro _ _; constructor <;> x86_norm <;> decide +kernel)
  case' k => x86_norm))

syntax "p256_memcmp_run_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| p256_memcmp_run_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      apply RegisterBlock.block_end
      intro s s' _ hH
      apply hH.weaken
      · x86_norm [$ls,*]
      · x86_norm [$ls,*]
      · intro i; cases i <;> x86_norm [$ls,*]
      · x86_norm [$ls,*]))

end P256.Proofs.Program.Compare
