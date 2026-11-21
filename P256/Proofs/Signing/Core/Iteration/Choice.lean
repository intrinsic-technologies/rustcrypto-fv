import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open ScalarFrame (choiceClobbers)

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (offset : Nat) (disp : BitVec 32)
    (bound : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + 5#64 ∧
      u.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept (choiceClobbers s 2280) t u := by
  obtain ⟨u, run, ready, sp, ip, value, agrees⟩ := ScalarFrame.choice_step pre.toCalleePre
    (frameOffset := 2280) (by decide) (by decide)
    (readyToStep frame.machine frame.bindingsSupported) frame.loaded frame.allocated frame.rsp
    offset disp bound bytes target rip
  have writes : WritesWithin (choiceClobbers s 2280)
      #v[registerRegion s .rdi 65, ScalarFrame.workRegion s 4584] := by
    intro c hc a ha
    simp only [choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals exact ⟨ScalarFrame.workRegion s 4584, by simp,
      ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  exact ⟨u, run, after_agrees pre frame ready agrees writes sp
    (by simp [choiceClobbers]) (by simp [choiceClobbers]) (by simp [choiceClobbers]),
    ip, value, agrees⟩

theorem choice_byte {s t u : RamState}
    (agrees : AgreesExcept (choiceClobbers s 2280) t u)
    {offset : Nat} (bound : offset < 2280) :
    u.external[frameBase s + BitVec.ofNat 64 offset]? =
      t.external[frameBase s + BitVec.ofNat 64 offset]? := by
  have address : frameBase s + BitVec.ofNat 64 offset =
      (stackPtr s - 2289) + BitVec.ofNat 64 (9+offset) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    congr 1
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have push : stackPtr s - BitVec.ofNat 64 (2280 + 8) = (stackPtr s - 2289) + 1 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  apply agrees.byte
  intro c hc cover
  simp only [choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact cover.elim
  · obtain ⟨i, hi, eq⟩ := cover
    apply RangeApart.offsets (stackPtr s - 2289) (a := 1) (b := 9+offset)
      (len := 8) (count := 1) (by decide) (by omega) (.inl (by omega)) i hi 0 (by decide)
    rw [address, push] at eq
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using eq.symm
  · obtain ⟨i, hi, eq⟩ := cover
    apply RangeApart.offsets (stackPtr s - 2289) (a := 0) (b := 9+offset)
      (len := 1) (count := 1) (by decide) (by omega) (.inl (by omega)) i hi 0 (by decide)
    rw [address] at eq
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using eq.symm

end P256.Proofs.Signing.Core.Iteration
