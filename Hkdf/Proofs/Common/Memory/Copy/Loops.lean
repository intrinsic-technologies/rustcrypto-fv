import Hkdf.Proofs.Common.Memory.Copy.Memory
import Hkdf.Proofs.Common.Memory.Copy.Movsb

set_option autoImplicit false

open Hkdf.Proofs.Program

open Hkdf.Proofs.Common.Machine (CalleePre)

namespace Hkdf.Proofs.Common.Memory.Copy

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem CopyState.repMovsb [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve count more : Nat} {p : BitVec 64}
    (hp : CalleePre s boundary 0x10dd60 n n reserve)
    (h : CopyState s t count) (hcount : count + more ≤ n)
    (hrip : t.RIP = p) (hc : rcx.read t = BitVec.ofNat 64 more)
    (hcode : CodeIn (codeRange p [0xf3, 0xa4]) t)
    (hprog : ∀ i < 2, InProgram (p + BitVec.ofNat 64 i))
    (hend : p + 2 ≠ boundary.rip) :
    ∃ u, Advances boundary (max more 1) t u ∧ CopyState s u (count+more) ∧
      u.RIP = p + 2#64 ∧ rcx.read u = 0 ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) more, .rip] t u := by
  have hn := sourceLow hp
  have hcn : (rcx.read t).toNat = more := by
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hz : more = 0
  · have hc0 : rcx.read t = 0#64 := by simpa only [hz] using hc
    simp only [hz, Nat.add_zero, Nat.zero_max]
    obtain ⟨ha, hr, hi, he, _⟩ := Movsb.rep_movsb_zero boundary p t h.ready hcode hrip hc0 hend
    refine ⟨nextState t, ha, ?_, hi, ?_, he.mono (by simp)⟩
    · simpa only [Nat.add_zero] using h.registers hr (he.mono (by simp [registerComponents]))
    · exact (he.read (by simp)).trans hc0
  · have pre : Movsb.RepMovsbPre p t := by
      refine ⟨hrip, by exact (h.agrees.directionFlagClear (by simp [copyComponents, registerComponents]) hp.directionFlag).df, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcn]; exact (h.sourceReadable hp hcount).low
      · rw [hcn]; exact (h.destinationReadable hp hcount).low
      · rw [hcn]; exact (h.sourceReadable hp hcount).mem
      · rw [hcn]; exact (h.destinationReadable hp hcount).mem
      · rw [hcn]; exact h.disjoint hp hcount
      · rw [hcn]; exact h.destinationTables hp hcount (by omega)
      · rw [hcn]; exact h.destinationCodeApart (bytes := [0xf3, 0xa4]) hp hcount hprog
    have hstart : p ≠ boundary.rip := by
      intro heq
      apply hp.outerBoundary
      have hi := hprog 0 (by decide)
      simpa only [BitVec.add_zero, heq] using hi
    have ha := Movsb.rep_movsb_advances hp.stride boundary p t h.ready hcode pre hstart hend
    obtain ⟨hr, _, he⟩ := Movsb.rep_movsb_steps hp.stride p t h.ready hcode pre
    have hcbytes := Movsb.rep_movsb_copy hp.stride p t h.ready hcode pre
    have hw := he.writes
    change _ ∧ _ ∧ _ ∧ _ at hw
    have hag := he.agrees
    rw [Movsb.repMovsbEffect_components, hcn] at hag
    rw [hcn] at ha hr he hw hcbytes
    change AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) more, .rip] t _ at hag
    refine ⟨_, ha, ?_, he.rip, hw.2.2.1, hag⟩
    · exact h.append hp hcount hr hw.1 hw.2.1 hcbytes hag

theorem rep_movsq_zero [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, 0x48, 0xa5]) s)
    (hrip : s.RIP = p) (hcount : rcx.read s = 0) (hend : p + 3#64 ≠ boundary.rip) :
    let t := nextState s
    Advances boundary 1 s t ∧ ReadyToStep t ∧ t.RIP = p + 3#64 ∧ AgreesExcept [.rip] s t := by
  have hs := rep_movsq_step_zero s h.midRep 0x48 (by simp [RexWPrefix])
    (hrip ▸ hcode.bytesAt) (hrip ▸ hcode.low (by simp) (by simp)) hcount
  dsimp only
  rw [nextState_of_step hs]
  have hag : AgreesExcept [.rip] s (repMovsqZeroAfter s) :=
    (AgreesExcept.repMovsqZero s).of_clearRep h.ready.repeatClear (repMovsqZeroAfter_repeat s)
  have hip : (repMovsqZeroAfter s).RIP = p + 3#64 := by
    rw [repMovsqZeroAfter_rip s h.ready.msr, hrip]
    rfl
  exact ⟨Advances.of_step hs (.inl (hip ▸ hend)),
    ReadyToStep.of_agreesExcept h hag h.memory.tables, hip, hag⟩

theorem CopyState.repMovsq [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve count words : Nat} {p : BitVec 64}
    (hp : CalleePre s boundary 0x10dd60 n n reserve)
    (h : CopyState s t count) (hcount : count + 8*words ≤ n)
    (hrip : t.RIP = p) (hc : rcx.read t = BitVec.ofNat 64 words)
    (hcode : CodeIn (codeRange p [0xf3, 0x48, 0xa5]) t)
    (hprog : ∀ i < 3, InProgram (p + BitVec.ofNat 64 i))
    (hend : p + 3 ≠ boundary.rip) :
    ∃ u, Advances boundary (max words 1) t u ∧ CopyState s u (count+8*words) ∧
      u.RIP = p + 3#64 ∧ rcx.read u = 0 ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) (8*words), .rip] t u := by
  have hn := sourceLow hp
  have hcn : (rcx.read t).toNat = words := by
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hz : words = 0
  · have hc0 : rcx.read t = 0#64 := by simpa only [hz] using hc
    simp only [hz, Nat.mul_zero, Nat.add_zero, Nat.zero_max]
    obtain ⟨ha, hr, hi, he⟩ := rep_movsq_zero boundary p t h.ready hcode hrip hc0 hend
    refine ⟨nextState t, ha, ?_, hi, ?_, he.mono (by simp)⟩
    · exact h.registers hr (he.mono (by simp [registerComponents]))
    · exact (he.read (by simp)).trans hc0
  · have pre : RepMovsqPre p t := by
      refine ⟨hrip, (h.agrees.directionFlagClear (by simp [copyComponents, registerComponents]) hp.directionFlag).df, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcn]; exact (h.sourceReadable hp hcount).low
      · rw [hcn]; exact (h.destinationReadable hp hcount).low
      · rw [hcn]; exact (h.sourceReadable hp hcount).mem
      · rw [hcn]; exact (h.destinationReadable hp hcount).mem
      · rw [hcn]; exact h.disjoint hp hcount
      · rw [hcn]; exact PageTableEntriesApart.of_frames (h.destinationTables hp hcount (by omega))
      · rw [hcn]; exact h.destinationCodeApart (bytes := [0xf3, 0x48, 0xa5]) hp hcount hprog
    have hstart : p ≠ boundary.rip := by
      intro heq
      apply hp.outerBoundary
      have hi := hprog 0 (by decide)
      simpa only [BitVec.add_zero, heq] using hi
    have ha := rep_movsq_advances hp.stride boundary p 0x48 (by simp [RexWPrefix]) t h.ready hcode pre hstart hend
    obtain ⟨hr, _, he⟩ := rep_movsq_steps hp.stride p 0x48 (by simp [RexWPrefix]) t h.ready hcode pre
    have hcbytes := rep_movsq_copy hp.stride p 0x48 (by simp [RexWPrefix]) t h.ready hcode pre
    have hw := he.writes
    change _ ∧ _ ∧ _ ∧ _ at hw
    have hag := he.agrees
    rw [repMovsqEffect_components, hcn] at hag
    rw [hcn] at ha hr he hw hcbytes
    change AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) (8*words), .rip] t _ at hag
    refine ⟨_, ha, ?_, he.rip, hw.2.2.1, hag⟩
    exact h.append hp hcount hr hw.1 hw.2.1 hcbytes hag

end Hkdf.Proofs.Common.Memory.Copy
