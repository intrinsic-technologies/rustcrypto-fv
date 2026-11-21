import Sha3.Proofs.Update.Division.Branch
import Sha3.Proofs.Update.Frame

namespace Sha3.Proofs.Update.Division

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def clobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 14, .reg 13, .reg 5, .reg 12, .flags, .rip]

structure Result (v : Variant) (n : Nat) (source : BitVec 64) (s : RamState) : Prop where
  full : s.regValue .r13 = BitVec.ofNat 64 (v.rate * (n / v.rate))
  remaining : s.regValue .r12 = BitVec.ofNat 64 (n % v.rate)
  input : s.regValue .rbx = source
  short : n / v.rate = 0 → s.RIP = tailAddress v
  blocks : 0 < n / v.rate →
    s.regValue .rbp = BitVec.ofNat 64 (v.rate * (n / v.rate)) ∧
    s.regValue .r14 = source ∧ s.RIP = fullBlockAddress v

theorem clobbers_nomem : ∀ c ∈ clobbers, ∀ address, ¬ c.Covers address := by
  simp [clobbers, Component.Covers]

private theorem length_frame {s t : RamState}
    (h : AgreesExcept (Length.clobbers 13) s t) : AgreesExcept clobbers s t :=
  h.mono (by simp [Length.clobbers, clobbers])

private theorem setup_frame {s t : RamState}
    (h : AgreesExcept setupClobbers s t) : AgreesExcept clobbers s t :=
  h.mono (by simp [setupClobbers, clobbers])

private theorem frame_trans {s u t : RamState}
    (hsu : AgreesExcept clobbers s u) (hut : AgreesExcept clobbers u t) :
    AgreesExcept clobbers s t := (hsu.trans hut).mono (by
  intro c hc
  simpa only [List.mem_append, or_self] using hc)

theorem advance [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (n : Nat) (hn : n < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (ip : s.RIP = divisionAddress v) (input : s.regValue .r12 = BitVec.ofNat 64 n) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      Result v n (s.regValue .rbx) t ∧ AgreesExcept clobbers s t := by
  have hn64 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨u, hu, ru, lu, ipu, regs, au⟩ := length_setup v boundary (BitVec.ofNat 64 n)
    (by simpa only [hn64] using hn) s ready loaded hb ip input
  by_cases hshort : n < v.rate
  · obtain ⟨t, ht, rt, lt, ipt, finalRegs, ag⟩ := initial_taken v boundary
      (BitVec.ofNat 64 n) (by simpa only [hn64] using hn) u ru lu hb ipu regs
      (by simpa only [hn64] using hshort)
    have ha := frame_trans (length_frame au) (ag.mono (by simp [clobbers]))
    refine ⟨_, t, hu.trans ht, rt, lt, ⟨?_, ?_, ?_, fun _ ↦ ipt, ?_⟩, ha⟩
    · change (Operand.reg 13 : Operand 64).read t = _
      simpa only [hn64] using finalRegs.full
    · change (Operand.reg 12 : Operand 64).read t = _
      simpa only [hn64] using finalRegs.remaining
    · exact ha.read (n := 64) (r := 3) (by simp [clobbers])
    · intro hblocks
      have : n / v.rate = 0 := Nat.div_eq_of_lt hshort
      omega
  · obtain ⟨t, ht, rt, lt, ipt, finalRegs, count, source, ag⟩ := initial_fallthrough v boundary
      (BitVec.ofNat 64 n) (by simpa only [hn64] using hn) u ru lu hb ipu regs
      (by simpa only [hn64] using Nat.le_of_not_lt hshort)
    have ha := frame_trans (length_frame au) (setup_frame ag)
    refine ⟨_, t, hu.trans ht, rt, lt, ⟨?_, ?_, ?_, ?_, ?_⟩, ha⟩
    · change (Operand.reg 13 : Operand 64).read t = _
      simpa only [hn64] using finalRegs.full
    · change (Operand.reg 12 : Operand 64).read t = _
      simpa only [hn64] using finalRegs.remaining
    · exact ha.read (n := 64) (r := 3) (by simp [clobbers])
    · intro hzero
      have hpos := v.rate_pos
      have : 0 < n / v.rate := Nat.div_pos (Nat.le_of_not_lt hshort) hpos
      omega
    · intro _
      refine ⟨?_, ?_, ipt⟩
      · change (Operand.reg 5 : Operand 64).read t = _
        simpa only [hn64] using count
      · exact source.trans (au.read (by simp [Length.clobbers]))

theorem advance_invariant [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (hi : BodyInvariant initial s) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (n : Nat) (hn : n < 2 ^ 32)
    (ip : s.RIP = divisionAddress v) (input : s.regValue .r12 = BitVec.ofNat 64 n) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyInvariant initial t ∧
      Result v n (s.regValue .rbx) t ∧ AgreesExcept clobbers s t := by
  obtain ⟨fuel, t, ht, rt, _, result, ha⟩ := advance v boundary hb n hn s hi.ready hi.loaded
    ip input
  refine ⟨fuel, t, ht, hi.of_stateWrites hc rt ha ?_ (by simp [clobbers]), result, ha⟩
  intro c hmem address hcover
  exact (clobbers_nomem c hmem address hcover).elim

end Sha3.Proofs.Update.Division
