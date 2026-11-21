import Md5.Proofs.NewEntries.Reset.Prologue.Storage
import Md5.Proofs.NewEntries.Reset.Prologue.Branch

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Block Md5.Proofs.Streaming

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read BitVec.sub_eq_add_neg

structure ResetProloguePost (initial : RamState) (inputs : Array Slices.Input)
    (first : Nat) (final : RamState) : Prop extends ResetInitialized initial final where
  rip : final.RIP = if min first inputs.size = 0 then 0x1014e0 else 0x1013f8
  total : (Operand.mem (stackPtr final + 8) : Operand 64).read final =
    BitVec.ofNat 64 inputs.size
  count : (Operand.reg 12 : Operand 64).read final = BitVec.ofNat 64 (min first inputs.size)
  index : min first inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read final = 0
  empty : min first inputs.size = 0 →
    (Operand.reg 2 : Operand 64).read final = 0x1032547698badcfe ∧
    (Operand.reg 7 : Operand 64).read final = 0xefcdab8967452301 ∧
    (Operand.reg 6 : Operand 64).read final = BitVec.ofNat 64 inputs.size

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem reset_prologue_of_ready [bindings : Bindings] {s : RamState}
    {inputs : Array Slices.Input} {first : Nat} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hCall : ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices bindings s inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ ResetProloguePost s inputs first t := by
  have hFrame : PrologueFrame 0x101340 680 s :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable,
      (hCall.stackSeparation.2
        (Stack.region s ResetThenDigest.updateResetSlices.minStackBytes) (by simp)).2⟩
  obtain ⟨n, u, hInit, hu, hCodeU, hE⟩ :=
    reset_initialized boundary hReady hCode hFrame hOutside
  have hCommon := reset_initialized_common hFrame hE
  have hFirstU : (Operand.reg 1 : Operand 64).read u =
      (Operand.reg 1 : Operand 64).read s :=
    hE.agrees.read (by x86_norm [prologuePushEffect, resetInitEffect])
  have hCountU : (Operand.reg 6 : Operand 64).read u =
      (Operand.reg 6 : Operand 64).read s :=
    hE.agrees.read (by x86_norm [prologuePushEffect, resetInitEffect])
  have hW := hE.writes
  x86_norm [prologuePushEffect, resetInitEffect] at hW
  rcases hW with ⟨_, _, _, _, _, _, _, _, hBoundU, _, _, hHighU, _, hLowU, _⟩
  have hAddress : stackPtr u + 8 = stackPtr s - 352 := by
    rw [hCommon.rsp]
    simp only [Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have hWrite : Memory.MemWritable u (stackPtr u + 8) 8 := by
    rw [hAddress]
    have hw := hFrame.writable 352 8 (by decide) (by decide)
    exact ⟨hw.low, fun i hi ↦ hCommon.agrees.grow _ (hw.bytes i hi), hw.tables⟩
  have hAvoid : ∀ x ∈ Extracted.programImage,
      ¬ (Component.mem (stackPtr u + 8) 8).Covers x.1 := by
    rw [hAddress]
    exact hFrame.avoids_mem 352 8 (by decide) (by decide)
  obtain ⟨m, t, hBranch, ht, hCodeT, hRip, hBound, hIndex, hTotal, hAgrees⟩ :=
    reset_branch boundary ((Operand.reg 1 : Operand 64).read s)
      ((Operand.reg 6 : Operand 64).read s) hu hCodeU hE.rip hOutside
      hFirstU hBoundU hCountU hWrite hAvoid
  have hFirstNat : ((Operand.reg 1 : Operand 64).read s).toNat = first :=
    hCall.firstCountArgumentMatchesFirst
  have hCountNat : ((Operand.reg 6 : Operand 64).read s).toNat = inputs.size :=
    hCall.inputsInMemory.countArgument
  have hFirstZero : (Operand.reg 1 : Operand 64).read s = 0 ↔ first = 0 := by
    rw [BitVec.toNat_eq, hFirstNat]
    rfl
  have hCountZero : (Operand.reg 6 : Operand 64).read s = 0 ↔ inputs.size = 0 := by
    rw [BitVec.toNat_eq, hCountNat]
    rfl
  have hCountValue : (Operand.reg 6 : Operand 64).read s = BitVec.ofNat 64 inputs.size := by
    have hh := congrArg (BitVec.ofNat 64) hCountNat
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh
  have hEmptyIff : ((Operand.reg 1 : Operand 64).read s = 0 ∨
      (Operand.reg 6 : Operand 64).read s = 0) ↔ min first inputs.size = 0 := by
    rw [hFirstZero, hCountZero, Nat.min_eq_zero_iff]
  refine ⟨n + m, t, hInit.trans hBranch, ht, hCodeT, ?_⟩
  refine {
    toResetInitialized := reset_branch_storage hFrame hCommon hAgrees
    rip := by simpa only [hEmptyIff] using hRip
    total := hTotal.trans hCountValue
    count := by simpa only [hFirstNat, hCountNat] using hBound
    index := fun h ↦ hIndex (fun hz ↦ h (hEmptyIff.mp hz))
    empty := ?_
  }
  intro _
  exact ⟨(hAgrees.read (n := 64) (r := 2) (by simp)).trans hHighU,
    (hAgrees.read (n := 64) (r := 7) (by simp)).trans hLowU,
    (hAgrees.read (n := 64) (r := 6) (by simp)).trans (hCountU.trans hCountValue)⟩

end Md5.Proofs.NewEntries.Reset
