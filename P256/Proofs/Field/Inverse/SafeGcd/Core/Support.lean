import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Support
import P256.Proofs.Field.Inverse.SafeGcd.Frame

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Support

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Op : Nat → Type

def activation (s : RamState) (stackBytes : Nat) : Activation where
  original := s.external
  rsp := stackPtr s
  ret := (returnBoundary s).rip
  low := stackPtr s - BitVec.ofNat 64 stackBytes
  rbx := s.regValue .rbx
  rbp := s.regValue .rbp
  r12 := s.regValue .r12
  r13 := s.regValue .r13
  r14 := s.regValue .r14
  r15 := s.regValue .r15
  rdi := s.regValue .rdi
  rsi := s.regValue .rsi
  rdx := s.regValue .rdx
  rcx := s.regValue .rcx
  r8 := s.regValue .r8
  r9 := s.regValue .r9
  mxcsr := s.MXCSR
  ftw := (Operand.ftw : Operand 16).read s
  fcw := s.FP87_Control
  fs := s.FS

theorem activation_regs (s : RamState) (stackBytes : Nat) :
    ∀ r ∈ Activation.entryNumbers,
      (Reg.ofIndex r).read s = ⟨64, (activation s stackBytes).entryReg r⟩ := by
  intro r hr
  simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem atoms_locationOf [Bindings] {lifted : Lifted} {code : CodeMap}
    {loc : lifted.Location} {stack : List lifted.StackFrame} {s : RamState} {atoms : List Atom}
    (hrel : Lift.Rel code lifted ⟨loc, stack⟩ s)
    (hlive : ∀ atom ∈ atoms, match atom with
      | .reg r _ | .low r _ _ => Live (lifted.live loc.label) r
      | _ => True)
    (h : Atom.All code loc.arguments s.external atoms) :
    Atom.All code (lifted.locationOf loc.label s).arguments s.external atoms := by
  induction atoms with
  | nil => trivial
  | cons atom atoms ih =>
    refine ⟨?_, ih (fun a ha => hlive a (List.mem_cons_of_mem atom ha)) h.2⟩
    cases atom with
    | reg r v =>
      have hr := hrel.regs r r.isLt (hlive _ List.mem_cons_self)
      simpa only [Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn, hr] using h.1
    | low r n v =>
      have hr := hrel.regs r r.isLt (hlive _ List.mem_cons_self)
      simpa only [Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn, hr] using h.1
    | mem _ _ _ =>
      simpa only [Atom.All, Atom.Holds] using h.1
    | words _ _ _ =>
      simpa only [Atom.All, Atom.Holds] using h.1
    | readable _ _ =>
      simpa only [Atom.All, Atom.Holds] using h.1
    | writable _ _ =>
      simpa only [Atom.All, Atom.Holds] using h.1
    | fact _ =>
      simpa only [Atom.All, Atom.Holds] using h.1

theorem activation_entryAtoms {code : CodeMap} {s : RamState} (m : FrameInfo)
    (lifted : Lifted) (l : lifted.Label) (hcalls : m.callSlots = [])
    (hret : (returnBoundary s).rip.toNat < 2^32)
    (hslot : Readable s.external (stackPtr s) 8)
    (hwindow : Writable code s.external (stackPtr s - BitVec.ofNat 64 m.window) m.window)
    (hroom : m.window ≤ (stackPtr s).toNat)
    (halign : (stackPtr s).toNat % 16 = 8) (hdf : RFLAGS.DirectionFlagClear s.RFLAGS) :
    Atom.All code (lifted.locationOf l s).arguments s.external
      (FrameCompat.entryAtoms m (activation s m.window)) := by
  have hr : ∀ r ∈ Activation.entryNumbers, ∀ hi : r < Reg.count,
      (lifted.locationOf l s).arguments[r] =
        ⟨64, (activation s m.window).entryReg r⟩ := fun r hm _ =>
    (Vector.getElem_ofFn _).trans (activation_regs s _ r hm)
  unfold FrameCompat.entryAtoms FrameInfo.frameAtoms FrameCompat.entryFrame
  rw [Atom.all_append, Atom.all_append, Atom.all_append]
  refine ⟨⟨⟨⟨hr 4 (by decide) (by decide),
    (Vector.getElem_ofFn _).trans (Reg.read_df_iff.2 hdf), ?_⟩, trivial⟩, ?_⟩, ?_⟩
  · simp only [FrameCompat.entryRegs, List.map_cons, List.map_nil, Atom.All, Atom.Holds]
    exact ⟨hr 1 (by decide) (by decide), hr 2 (by decide) (by decide),
      hr 3 (by decide) (by decide), hr 5 (by decide) (by decide),
      hr 6 (by decide) (by decide), hr 7 (by decide) (by decide),
      hr 8 (by decide) (by decide), hr 9 (by decide) (by decide),
      hr 12 (by decide) (by decide), hr 13 (by decide) (by decide),
      hr 14 (by decide) (by decide), hr 15 (by decide) (by decide),
      trivial⟩
  · unfold FrameInfo.stackAtoms
    rw [Atom.all_append, Atom.all_append]
    refine ⟨⟨⟨hslot, rfl, hret, trivial⟩, ?_⟩, halign, trivial⟩
    have hmod : (BitVec.ofNat 64 m.window).toNat = m.window :=
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hroom (stackPtr s).isLt)
    have hlow : (stackPtr s - BitVec.ofNat 64 m.window).toNat + m.window ≤ (stackPtr s).toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hmod]; exact hroom), hmod]
      omega
    split
    · exact ⟨by change (stackPtr s - BitVec.ofNat 64 m.window).toNat ≤ (stackPtr s).toNat; omega, trivial⟩
    · exact ⟨hwindow, hlow, trivial⟩
  · simp only [hcalls, FrameInfo.callSlotAtoms, Atom.All]

theorem ahead_call_advances [Bindings] {lifted : Lifted} {code : CodeMap}
    {boundary : ReturnBoundary} {initial : RamState} {loc : lifted.Location}
    {stack : List lifted.StackFrame} {Q : lifted.Location → lifted.StackFrame → Prop}
    (sim : Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (hrel : Lift.Rel code lifted ⟨loc, stack⟩ initial)
    (hahead : Ahead lifted code (fun l ↦ CallTo Q (lifted.program.runBlock (dialect code) l)) loc) :
    ∃ fuel final callee frame, Advances boundary fuel initial final ∧
      Lift.Rel code lifted ⟨callee, frame :: stack⟩ final ∧ Q callee frame := by
  obtain ⟨last, hjump, hcall⟩ := hahead
  cases hc : lifted.program.runBlock (dialect code) last with
  | call callee frame =>
    have hs : (lifted.program.sem (dialect code)).Step ⟨last, stack⟩
        ⟨callee, frame :: stack⟩ := by
      simp only [Program.sem, Program.step, hc, Transfer.next]
    obtain ⟨final, hrun, hfinal⟩ := sim.reaches ((hjump.reaches stack).tail hs) hrel
    obtain ⟨fuel, hfuel⟩ := machine_reaches_iff.mp hrun
    exact ⟨fuel, final, callee, frame, hfuel, hfinal, by simpa only [hc, CallTo] using hcall⟩
  | jump l => simp only [hc, CallTo] at hcall
  | returned o => simp only [hc, CallTo] at hcall
  | stuck => simp only [hc, CallTo] at hcall

theorem ahead_return_returns [Bindings] {lifted : Lifted} {code : CodeMap}
    {boundary : ReturnBoundary} {initial : RamState} {loc : lifted.Location}
    {Q : Output Value Ram Reg.count → Prop}
    (sim : Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (hrel : Lift.Rel code lifted ⟨loc, []⟩ initial)
    (hahead : Ahead lifted code (fun l ↦ ReturnOf Q (lifted.program.runBlock (dialect code) l)) loc)
    (hon : ∀ lo final, Q lo → Lift.RetRel code lifted lo final → AtBoundary boundary final) :
    ∃ fuel final lo, Returns boundary fuel initial final ∧
      Lift.RetRel code lifted lo final ∧ Q lo := by
  obtain ⟨fuel, final, lo, hex, hrel, hq⟩ := Correction.Execution.ahead_return_run sim hrel hahead
  exact ⟨fuel, final, lo, hex.resolve_left (fun h => h.2 (hon lo final hq hrel)), hrel, hq⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Support
