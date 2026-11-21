import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Loop.Invariant
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Pair
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Tail

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

theorem mixedLoopStep [Bindings] {boundary : ReturnBoundary} {src dst : BitVec 64}
    {index : Nat} {hi lo : UInt8} {input : List UInt8} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : OutsideMixed boundary.rip)
    (h : MixedLoopPre src dst index (hi :: lo :: input) s)
    (hEven : input.length % 2 = 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      MixedLoopPre src dst (index + 1) input t ∧
      t.regValue .rsi = s.regValue .rsi ||| ((pairWord hi lo).extractLsb' 8 8).setWidth 64 ∧
      t.external[dst + BitVec.ofNat 64 index]? = some ((⟨(pairWord hi lo).setWidth 8⟩ : UInt8)) ∧
      AgreesExcept (mixedLoopChanges (dst + BitVec.ofNat 64 index) 1) s t := by
  obtain ⟨hHiRead, hHiByte, hLoRead, hLoByte⟩ := h.read_pair
  have hEntry : s.RIP = 0x1001f0 := by
    simpa only [mixedLoopPC, List.cons_ne_nil, ite_false] using h.rip
  obtain ⟨pairFuel, u, hPairRun, hReadyU, hCodeU, hRipU, hWordU, hPairFrame⟩ :=
    pair_advances hReady hCode hOutside hEntry hHiRead hHiByte hLoRead hLoByte
  have hR9 : u.regValue .r9 = s.regValue .r9 :=
    hPairFrame.read (n := 64) (r := 9) (by simp)
  have hRsi : u.regValue .rsi = s.regValue .rsi :=
    hPairFrame.read (n := 64) (r := 6) (by simp)
  have hRcx : u.regValue .rcx = s.regValue .rcx :=
    hPairFrame.read (n := 64) (r := 1) (by simp)
  have hRax : u.regValue .rax = s.regValue .rax :=
    hPairFrame.read (n := 64) (r := 0) (by simp)
  have hAddress : u.regValue .rcx + u.regValue .rax = dst + BitVec.ofNat 64 index := by
    rw [hRcx, hRax, h.rcx, h.rax]
  have hWritable : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable u (u.regValue .rcx + u.regValue .rax) 1 := by
    rw [hAddress]
    exact writable_of_agrees (by
      simpa only [BitVec.add_zero] using writable_sub h.output 0 1
        (by simp only [List.length_cons]; omega)) hPairFrame
  have hAvoid : ¬ InProgram (u.regValue .rcx + u.regValue .rax) := by
    rw [hAddress]
    simpa only [BitVec.add_zero] using h.avoid 0 (by simp only [List.length_cons]; omega)
  obtain ⟨tailFuel, t, hTailRun, hReadyT, hCodeT, hRipT, hIndexT, hAccumulatorT,
    hByteT, hTailFrame⟩ := tail_advances hReadyU hCodeU hRipU hWritable hAvoid hOutside
  have hFrame : AgreesExcept (mixedLoopChanges (dst + BitVec.ofNat 64 index) 1) s t := by
    rw [hAddress] at hTailFrame
    exact (hPairFrame.trans hTailFrame).mono (by simp [mixedLoopChanges])
  have hNextRip : t.RIP = mixedLoopPC input := by
    rw [hR9, hRax] at hRipT
    exact hRipT.trans (h.next_rip hEven)
  have hNextIndex : t.regValue .rax = BitVec.ofNat 64 (index + 1) := by
    rw [hRax, h.rax] at hIndexT
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add] using hIndexT
  have hAccumulator : t.regValue .rsi =
      s.regValue .rsi ||| ((pairWord hi lo).extractLsb' 8 8).setWidth 64 := by
    change u.regValue .rbx = (pairWord hi lo).setWidth 64 at hWordU
    rw [hRsi, hWordU, pairWord_accumulate_eq _ _ _ h.accumulator] at hAccumulatorT
    exact hAccumulatorT
  have hNextAcc : t.regValue .rsi = 0 ∨ t.regValue .rsi = 255 := by
    rw [hAccumulator]
    exact pairWord_accumulate_cases _ _ _ h.accumulator
  refine ⟨pairFuel + tailFuel, t, hPairRun.trans hTailRun, hReadyT, hCodeT,
    h.next hFrame hNextRip hNextIndex hNextAcc, hAccumulator, ?_, hFrame⟩
  rw [hAddress] at hByteT
  change u.regValue .rbx = (pairWord hi lo).setWidth 64 at hWordU
  rw [hWordU] at hByteT
  have hUInt : UInt8.ofNat ((pairWord hi lo).setWidth 8).toNat =
      (⟨(pairWord hi lo).setWidth 8⟩ : UInt8) := UInt8.ofNat_toNat
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), hUInt] using hByteT

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
