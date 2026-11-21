import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Prepare
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Loop
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Outcome
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Tail.Epilogue
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Tail.Short

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

theorem mixed_positive_finish [Bindings] {initial u s : RamState} {input : List UInt8}
    {capacity : Nat} {boundary : ReturnBoundary}
    (hCall : MixedInternalCall initial input capacity boundary)
    (hStart : MixedPositiveStart initial input u)
    (hLoop : MixedLoopResult (initial.regValue .rcx) 0 input u s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFit : input.length / 2 ≤ capacity) :
    ∃ fuel t, Returns boundary fuel s t ∧ t.RIP = boundary.rip ∧
      stackPtr t = boundary.rsp ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      AgreesExcept (mixedCallChanges initial (input.length / 2) (mixedDecodeList input).isSome) initial t ∧
      t.regValue .rbx = initial.regValue .rbx ∧
      t.regValue .rbp = initial.regValue .rbp ∧
      t.regValue .r14 = initial.regValue .r14 ∧
      match mixedDecodeList input with
      | none => t.regValue .rax = 2
      | some output => t.regValue .rax = 0 ∧
          (Operand.mem (initial.regValue .rdx) : Operand 64).read t =
            BitVec.ofNat 64 output.length ∧
          ∀ j (hj : j < output.length),
            t.external[initial.regValue .rcx + BitVec.ofNat 64 j]? = some output[j] := by
  have hf : AgreesExcept (mixedLoopChanges (initial.regValue .rcx) (input.length / 2)) u s := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hLoop.frame
  have sp : stackPtr s = stackPtr initial - 24 :=
    (hf.read (n := 64) (r := 4) (by simp [mixedLoopChanges])).trans hStart.stack
  have ax : s.regValue .r9 = BitVec.ofNat 64 (input.length / 2) :=
    (hf.read (n := 64) (r := 9) (by simp [mixedLoopChanges])).trans
      (by
        change u.regValue .r9 = _
        simpa only [BitVec.ofNat_eq_ofNat, Nat.zero_add] using hStart.pre.r9)
  have dx : (Operand.reg 6 : Operand 16).read s = (mixedLoopMarker input).setWidth 16 := by
    change (s.regValue .rsi).setWidth 16 = _
    simpa only [BitVec.ofNat_eq_ofNat, hStart.accumulator, BitVec.zero_or] using
      congrArg (BitVec.setWidth 16) hLoop.accumulator
  have saved (offset : Nat) (ho : offset + 8 ≤ 24) :
      memLoad s.external (stackPtr initial - 24 + BitVec.ofNat 64 offset) 64 =
      memLoad u.external (stackPtr initial - 24 + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
    apply hf.byte
    intro c hc hv
    simp only [mixedLoopChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    obtain ⟨j, hj, he⟩ := hv
    apply hCall.outputStack j (by omega) (offset + i) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add] using he.symm
  have rd : MemReadable s (stackPtr initial - 24) 24 := readable_of_agrees hStart.readable hf
  obtain ⟨v, adv, rv, cv, pc, statusv, bx, r14, bp, spv, fv⟩ := epilogue_advances hReady hCode hLoop.rip
    (by simpa only [BitVec.ofNat_eq_ofNat, sp, BitVec.add_zero] using readable_sub rd 0 8 (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, sp] using readable_sub rd 8 8 (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, sp] using readable_sub rd 16 8 (by decide)) hCall.returnOutside
  have hp : AgreesExcept (mixedCallChanges initial (input.length / 2) false) initial v :=
    ((hStart.frame.trans hf).trans fv).mono (by simp [mixedCallChanges, mixedLoopChanges])
  have di : v.regValue .rdx = initial.regValue .rdx := hp.read (n := 64) (r := 2) (by simp [mixedCallChanges])
  have spv' : stackPtr v = stackPtr initial := by
    rw [sp] at spv
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel] using spv
  have axv : v.regValue .r9 = BitVec.ofNat 64 (input.length / 2) :=
    (fv.read (n := 64) (r := 9) (by simp)).trans ax
  have stackEq (a : BitVec 64) : a - 24 + 8 = a - 16 ∧ a - 24 + 16 = a - 8 := by
    constructor <;> simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
  have bxv : v.regValue .rbx = initial.regValue .rbx := by
    change v.regValue .rbx = memLoad s.external (stackPtr s) 64 at bx
    rw [sp, ← BitVec.add_zero (stackPtr initial - 24), saved 0 (by decide)] at bx
    exact bx.trans (by simpa only [BitVec.add_zero] using hStart.savedRbx)
  have bpv : v.regValue .rbp = initial.regValue .rbp := by
    change v.regValue .rbp = memLoad s.external (stackPtr s + 16) 64 at bp
    rw [sp] at bp
    have hs := saved 16 (by decide)
    change memLoad s.external (stackPtr initial - 24 + 16) 64 =
      memLoad u.external (stackPtr initial - 24 + 16) 64 at hs
    rw [hs, (stackEq _).2] at bp
    exact bp.trans hStart.savedRbp
  have r14v : v.regValue .r14 = initial.regValue .r14 := by
    change v.regValue .r14 = memLoad s.external (stackPtr s + 8) 64 at r14
    rw [sp] at r14
    have hs := saved 8 (by decide)
    change memLoad s.external (stackPtr initial - 24 + 8) 64 =
      memLoad u.external (stackPtr initial - 24 + 8) 64 at hs
    rw [hs, (stackEq _).1] at r14
    exact r14.trans hStart.savedR14
  have ret : stackTop v = boundary.rip := by
    change memLoad v.external (stackPtr v) 64 = _
    rw [spv', ← hCall.returnValue]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
    apply ((hStart.frame.trans hf).trans fv).byte
    intro c hc hv
    simp only [List.mem_append, mixedLoopChanges, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with (hc | hc) | hc
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hv.elim
      obtain ⟨j, hj, he⟩ := hv
      exact hCall.returnStackApart i hi j hj he
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hv.elim
      obtain ⟨j, hj, he⟩ := hv
      exact hCall.returnOutput i hi j (by omega) he
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hv.elim
  have rdv : MemReadable v (stackPtr v) 8 := by
    rw [spv']; exact readable_of_agrees hCall.returnRead hp
  have rspv : stackPtr v + 8 = boundary.rsp := by rw [spv', hCall.returnStack]
  have low : boundary.rip.toNat < userAddressLimit := hCall.returnLow
  cases hd : mixedDecodeList input with
  | none =>
    have hm : mixedLoopMarker input = 255 := by
      rcases mixedLoopMarker_eq_zero_or input with hz | hz
      · have hv := (mixedLoopMarker_eq_zero_iff input).mp hz
        simp [hd] at hv
      · exact hz
    have pcv : v.RIP = 0x1002fa := by
      rw [dx, hm] at pc
      exact pc.trans (by decide +kernel)
    obtain ⟨t, rt, ripT, rspT, ready, codeT, ft⟩ := common_return rv cv (Or.inl pcv)
      rdv ret rspv low
    refine ⟨7, t, adv.returns rt, ripT, rspT, ready, codeT, ?_, ?_, ?_, ?_, (ft.read (n := 64) (r := 0) (by simp)).trans statusv⟩
    · exact (hp.trans ft).mono (by simp [mixedCallChanges])
    · exact (ft.read (n := 64) (r := 3) (by simp)).trans bxv
    · exact (ft.read (n := 64) (r := 5) (by simp)).trans bpv
    · exact (ft.read (n := 64) (r := 14) (by simp)).trans r14v
  | some output =>
    have hm : mixedLoopMarker input = 0 :=
      (mixedLoopMarker_eq_zero_iff input).mpr (by simp [hd])
    have pcv : v.RIP = 0x100300 := by
      rw [dx, hm] at pc
      exact pc.trans (by decide +kernel)
    have hs : ∃ output, mixedDecodeList input = some output := ⟨output, hd⟩
    have wr : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable v (v.regValue .rdx) 8 := by
      rw [di]
      exact writable_of_agrees (hCall.result hFit hs) hp
    have avoid : ∀ i < 8, ¬ InProgram (v.regValue .rdx + BitVec.ofNat 64 i) := by
      simpa only [di] using hCall.resultAvoids hFit hs
    have apart : RangeApart (v.regValue .rdx) 8 (stackPtr v) 8 := by
      intro i hi j hj he
      apply hCall.returnResult hFit hs j hj i hi
      simpa only [di, spv'] using he.symm
    obtain ⟨t, rt, ripT, rspT, ready, codeT, len, status, ft⟩ := mixed_success_return rv cv pcv
      wr avoid apart rdv ret rspv low hCall.returnOutside
    refine ⟨9, t, adv.returns rt, ripT, rspT, ready, codeT, ?_, ?_, ?_, ?_, status, ?_, ?_⟩
    · have ft' := ft
      rw [di] at ft'
      exact (((hStart.frame.trans hf).trans fv).trans ft').mono
        (by simp [mixedCallChanges, mixedLoopChanges])
    · exact (ft.read (n := 64) (r := 3) (by simp)).trans bxv
    · exact (ft.read (n := 64) (r := 5) (by simp)).trans bpv
    · exact (ft.read (n := 64) (r := 14) (by simp)).trans r14v
    · simpa only [di, axv, mixedDecodeList_length_div_two hd] using len
    · intro j hj
      have eqv : v.external = s.external := fv.external (by simp [Component.Covers])
      rw [ft.byte ?_, eqv]
      · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hLoop.bytes_of_decode hd j hj
      · intro c hc hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        all_goals try exact hv.elim
        obtain ⟨i, hi, he⟩ := hv
        apply hCall.resultOutput hFit hs i hi j (by rw [mixedDecodeList_length_div_two hd] at hj; exact hj)
        simpa only [di] using he.symm

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
