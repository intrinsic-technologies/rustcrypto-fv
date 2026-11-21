import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false
namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Choice
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def components (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .flags, .rip,
    .mem (stackPtr s - 769) 9]

theorem byte_preserved {s t u : RamState} (h : AgreesExcept (components s) t u)
    {offset len : Nat} (ho : offset ≤ 760) (hl : len ≤ offset+8) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc hv
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  obtain ⟨j,hj,he⟩ := hv
  have ha : stackPtr s - BitVec.ofNat 64 offset =
      (stackPtr s - 769) + BitVec.ofNat 64 (769-offset) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 769 offset (by omega) (by omega)]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [← BitVec.add_assoc (-(769 : BitVec 64)),
      show -(769 : BitVec 64)+769#64=0#64 by decide +kernel, BitVec.zero_add]
  apply RangeApart.offsets (stackPtr s-769) (a := 0) (b := 769-offset)
    (len := 9) (count := len) (by decide) (by omega) (.inl (by omega)) j hj i hi
  rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, ← ha]
  exact he.symm

theorem read_preserved {s t u : RamState} (h : AgreesExcept (components s) t u)
    {offset n : Nat} (ho : offset ≤ 760) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s-BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s-BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun x : Option UInt8 => x.getD 0) (byte_preserved h ho hl hi)

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1100d0 65 80 3360) (state : Frame s t)
    (offset : Nat) (disp : BitVec 32) (hsize : offset+5 < 118431)
    (hbytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress+BitVec.ofNat 64 offset+(5 : BitVec 64) ∧
      (Operand.reg 0 : Operand 64).read u = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (components s) t u := by
  obtain ⟨u, run, ready, sp, ip, ax, agrees⟩ := ScalarFrame.choice_step pre
    (frameOffset := 760) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp
    offset disp hsize hbytes target rip
  have narrow : AgreesExcept [.reg 0, .flags, .rip,
      .mem (stackPtr s - 768) 8, .mem (stackPtr s - 769) 1] t u := by
    apply agrees.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0, .flags, .rip,
      .mem (stackPtr s - 768) 8, .mem (stackPtr s - 769) 1]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨ScalarFrame.workRegion s 3360, by simp,
      ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  refine ⟨6, u, run, state.after_effect pre (by decide) ready narrow writes
    (by simp), ip, ax, ?_⟩
  apply agrees.widen
  · intro c hc hm
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp [components]
  · intro a c hc ha
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    · refine ⟨.mem (stackPtr s - 769) 9, by simp [components], 1+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(769 : BitVec 64))]
      rfl
    · exact ⟨.mem (stackPtr s - 769) 9, by simp [components], i, by omega, rfl⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Choice
