import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
import P256.Proofs.Common.Refine.Contract
import P256.Proofs.Common.Refine.Tactic
import P256.Proofs.Program.Entry

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem rangeApart_of_notCode {code : CodeMap} {a p : BitVec 64} {len codeLen : Nat}
    (hc : ∀ j < codeLen, CodeAt code (p + BitVec.ofNat 64 j))
    (ha : ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i) :
    RangeApart a len p codeLen := by
  intro i hi j hj he
  obtain ⟨b, hb⟩ := hc j hj
  exact ha _ hb i hi he.symm
theorem writable_codeApart {code : CodeMap} {mem : Ram} {a p : BitVec 64}
    {len n : Nat} (hw : Writable code mem a len)
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (hstart : 0x100000 ≤ p.toNat) (hend : p.toNat + n ≤ 0x100000 + 118431) :
    RangeApart a len p n := by
  apply rangeApart_of_notCode _ hw.notCode
  intro j hj
  have hp : p.toNat + j < 0x100000 + 118431 := by omega
  have he : (p + BitVec.ofNat 64 j).toNat = p.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hi : p.toNat + j - 0x100000 < P256.Spec.Program.Extracted.textBytes.toList.length := by
    rw [chunked_toList_length, P256.Proofs.Program.textBytes_size]
    omega
  have hm := mem_codeRange P256.Spec.Program.Extracted.textAddress
    P256.Spec.Program.Extracted.textBytes.toList (p.toNat + j - 0x100000) hi
  have ha : P256.Spec.Program.Extracted.textAddress +
      BitVec.ofNat 64 (p.toNat + j - 0x100000) = p + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    rw [he, BitVec.toNat_add, BitVec.toNat_ofNat]
    change (1048576 + (p.toNat + j - 1048576) % 2^64) % 2^64 = p.toNat + j
    omega
  rw [ha] at hm
  refine ⟨P256.Spec.Program.Extracted.textBytes.toList[p.toNat + j - 0x100000], hcode _ ?_⟩
  simpa only [Machine.fnCode, Machine.sections, Machine.textSection,
    ImageSection.toCodeMap, ImageSections.toCodeMap, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using hm

theorem page_of_mod_sixteen {a : BitVec 64} {n : Nat}
    (h : a.toNat % 16 + n ≤ 16) : a.toNat % 4096 + n ≤ 4096 := by
  have hm : (a.toNat % 4096) % 16 = a.toNat % 16 := Nat.mod_mod_of_dvd _ (by decide)
  have hb := Nat.mod_lt a.toNat (by decide : 0 < 4096)
  omega

theorem ahead_return_run [Bindings] {lifted : Lifted} {code : CodeMap}
    {boundary : ReturnBoundary} {initial : RamState} {loc : lifted.Location}
    {Q : Output Value Ram Reg.count → Prop}
    (sim : Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (hrel : Lift.Rel code lifted ⟨loc, []⟩ initial)
    (hahead : Ahead lifted code (fun l ↦ ReturnOf Q (lifted.program.runBlock (dialect code) l)) loc)
    : ∃ fuel final lo, ((Advances boundary fuel initial final ∧ ¬ AtBoundary boundary final) ∨
      Returns boundary fuel initial final) ∧
      Lift.RetRel code lifted lo final ∧ Q lo := by
  obtain ⟨last, hjump, hret⟩ := hahead
  cases hc : lifted.program.runBlock (dialect code) last with
  | returned lo =>
    have hq : Q lo := by simpa only [hc, ReturnOf] using hret
    have hs : (lifted.program.sem (dialect code)).Ret ⟨last, []⟩ lo := by
      simp only [Program.sem, Program.step, hc, Transfer.next]
    obtain ⟨final, he, hfinal⟩ := sim.exec ((hjump.reaches []).exec (.ret hs)) hrel
    obtain ⟨mid, hsteps, n, hn⟩ := Semantics.exec_iff.mp he
    obtain ⟨m, hm⟩ := machine_reaches_iff.mp hsteps
    rcases hn with ⟨hadv, hoff⟩ | hreturns
    · exact ⟨m + n, final, lo, Or.inl ⟨hm.trans hadv, hoff⟩, hfinal, hq⟩
    · exact ⟨m + n, final, lo, Or.inr (hm.returns hreturns), hfinal, hq⟩
  | jump l => simp only [hc, ReturnOf] at hret
  | call l fr => simp only [hc, ReturnOf] at hret
  | stuck => simp only [hc, ReturnOf] at hret


theorem ahead_return_advances [Bindings] {lifted : Lifted} {code : CodeMap}
    {boundary : ReturnBoundary} {initial : RamState} {loc : lifted.Location}
    {Q : Output Value Ram Reg.count → Prop}
    (sim : Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (hrel : Lift.Rel code lifted ⟨loc, []⟩ initial)
    (hahead : Ahead lifted code (fun l ↦ ReturnOf Q (lifted.program.runBlock (dialect code) l)) loc)
    (hoff : ∀ lo final, Q lo → Lift.RetRel code lifted lo final → ¬ AtBoundary boundary final) :
    ∃ fuel final lo, Advances boundary fuel initial final ∧
      Lift.RetRel code lifted lo final ∧ Q lo := by
  obtain ⟨fuel, final, lo, hex, hrel, hq⟩ := ahead_return_run sim hrel hahead
  exact ⟨fuel, final, lo, (hex.resolve_right
    (fun h => hoff lo final hq hrel (Returns.atBoundary h))).1, hrel, hq⟩


end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
