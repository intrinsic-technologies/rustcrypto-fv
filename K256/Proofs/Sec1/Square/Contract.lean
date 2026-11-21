import K256.Proofs.Sec1.LIR
import K256.Proofs.Sec1.Square.Block

namespace K256.Proofs.Sec1.Square

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude
open Common.Field
open LIR (lifted)
open LIR.Fn1145f0 (frameInfo)

theorem call (code : CodeMap) (fr : Activation) (s : Store) (l : lifted.Location)
    (hrel : layout.Rel code (fr, ()) ⟨.entry, #v[], s⟩ l) :
    ∃ lo, lifted.program.Exec (Lift.dialect code) ⟨l, []⟩ lo ∧
      layout.RetRel code (fr, ()) ⟨#v[], none, (s.1, squareWords s.1)⟩ lo ∧
      Atom.All code lo.values lo.store (frameInfo.doneAtoms fr) :=
  LIR.Fn1145f0.call (blocks code) (exec s) fr () hrel

theorem routine [inst : Bindings] {code : CodeMap} {initial : RamState} {fr : Activation}
    {n : Nat} {regions : Vector MemoryRegion n} (s : Store)
    (hstride : UnitStringStride inst) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hready : EntryReady code initial) (hpre : LIR.Fn1145f0.Pre code fr initial)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) →
      ∀ r ∈ fr.region :: core.footprint () fr, ¬ r.Contains x)
    (hcore : Atom.All code (lifted.locationOf .l1145f0 initial).arguments initial.external
      (core.atoms .entry () fr s)) :
    RoutineResult inst initial regions fun t =>
      Execution.CallingConvention.SysVCalleeReturn initial t fr.ret ∧
      LIR.Fn1145f0.Post fr (core.footprint () fr) t ∧
      (Operand.reg 0 : Operand 64).read t = fr.rdi ∧
      WordsAt t.external fr.rsi 64 s.1 ∧ WordsAt t.external fr.rdi 64 (squareWords s.1) := by
  obtain ⟨k, t, hu, hs, hw, hd, hret, hpost, r, heq, lo, hr, hatoms⟩ :=
    LIR.Fn1145f0.routine core (LIR.blocks hstride code hcode) (blocks code) hready hpre hregions
      (lab := .entry) (p := s) (exec s) hcore
  have hresult := congrArg CFG.Output.store heq
  change (s.1, squareWords s.1) = r at hresult
  subst r
  obtain ⟨hreg, hin, hout, _⟩ := hatoms
  refine ⟨k, t, hu, hs, hw, hd, hret, hpost, ?_, hr.store ▸ hin, hr.store ▸ hout⟩
  exact Value.eq_bits ((hr.regs 0 (by decide) (by decide)).symm.trans hreg)

end K256.Proofs.Sec1.Square
