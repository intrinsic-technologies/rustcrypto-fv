import P256.Proofs.Program.Compare.Loop
import P256.Proofs.Program.Compare.Advance

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program.Compare.Ranges (memReadable_slice)

def scanChanges : List Component :=
  [.reg 0, .reg 3, .reg 7, .reg 11, .reg 12, .reg 14, .reg 15, .flags, .rip]

structure ScanPre (count : Nat) (s : RamState) : Prop where
  rip : s.RIP = 0x11c890
  bound : (Operand.reg 8 : Operand 64).read s =
    (Operand.reg 11 : Operand 64).read s + BitVec.ofNat 64 (16 * count)
  left : MemReadable s (leftAddress s) (16 * count)
  right : MemReadable s (rightAddress s) (16 * count)

def ScanOutcome (count : Nat) (s t : RamState) : Prop :=
  (t.RIP = 0x11c8bc ∧ BytesEqual s (leftAddress s) (rightAddress s) (16 * count)) ∨
  (t.RIP = 0x11c8d0 ∧ ¬ BytesEqual s (leftAddress s) (rightAddress s) (16 * count) ∧
    ((Operand.reg 0 : Operand 64).read t ≠ (Operand.reg 7 : Operand 64).read t ∨
      (Operand.reg 3 : Operand 64).read t ≠ (Operand.reg 14 : Operand 64).read t))

theorem ScanPre.chunk {s : RamState} {count : Nat} (h : ScanPre (count + 1) s) : ChunkPre s := by
  refine ⟨h.rip, ?_, ?_, ?_, ?_⟩
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using memReadable_slice h.left 0 8 (by omega)
  · exact memReadable_slice h.left 8 8 (by omega)
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using memReadable_slice h.right 0 8 (by omega)
  · exact memReadable_slice h.right 8 8 (by omega)

theorem chunk_frame {s t : RamState} (h : (chunkBranchEffect s).Holds s t) :
    AgreesExcept scanChanges s t :=
  h.agrees.mono (by simp [chunkBranchEffect, chunkEffect, Effect.components, scanChanges])

theorem advance_frame {s t : RamState} (h : (advanceEffect s).Holds s t) :
    AgreesExcept scanChanges s t :=
  h.agrees.mono (by simp [advanceEffect, incrementEffect, Effect.components, scanChanges])

theorem scan_frame_trans {s t u : RamState} (h : AgreesExcept scanChanges s t)
    (h' : AgreesExcept scanChanges t u) : AgreesExcept scanChanges s u :=
  (h.trans h').mono (by simp)

theorem scan_advance_values {s u t : RamState}
    (hc : (chunkBranchEffect s).Holds s u) (ha : (advanceEffect u).Holds u t) :
    (Operand.reg 8 : Operand 64).read t = (Operand.reg 8 : Operand 64).read s ∧
    (Operand.reg 11 : Operand 64).read t = (Operand.reg 11 : Operand 64).read s + 16 ∧
    leftAddress t = leftAddress s + 16 ∧ rightAddress t = rightAddress s + 16 := by
  have h8 := hc.agrees.read (n := 64) (r := 8)
    (by simp [chunkBranchEffect, chunkEffect, Effect.components])
  have h11 := hc.agrees.read (n := 64) (r := 11)
    (by simp [chunkBranchEffect, chunkEffect, Effect.components])
  have hf := scan_frame_trans (chunk_frame hc) (advance_frame ha)
  have h6 := hf.read (n := 64) (r := 6) (by decide)
  have h2 := hf.read (n := 64) (r := 2) (by decide)
  have ht8 := ha.agrees.read (n := 64) (r := 8)
    (by simp [advanceEffect, incrementEffect, Effect.components])
  have ht11 : (Operand.reg 11 : Operand 64).read t =
      (Operand.reg 11 : Operand 64).read s + 16 := by
    simpa only [advanceEffect, incrementEffect, Write.AllHold, h11] using ha.writes
  exact ⟨ht8.trans h8, ht11,
    by simp only [leftAddress, h6, ht11, BitVec.add_assoc],
    by simp only [rightAddress, h2, ht11, BitVec.add_assoc]⟩

theorem scan_advance_rip {s u t : RamState} {count : Nat} (hp : ScanPre (count + 1) s)
    (hc : (chunkBranchEffect s).Holds s u) (ha : (advanceEffect u).Holds u t) :
    t.RIP = if count = 0 then 0x11c8bc else 0x11c890 := by
  have h8 := hc.agrees.read (n := 64) (r := 8)
    (by simp [chunkBranchEffect, chunkEffect, Effect.components])
  have h11 := hc.agrees.read (n := 64) (r := 11)
    (by simp [chunkBranchEffect, chunkEffect, Effect.components])
  have heq : ((Operand.reg 8 : Operand 64).read u ==
      (Operand.reg 11 : Operand 64).read u + 16) = decide (count = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, h8, h11, hp.bound, BitVec.add_right_inj]
    constructor
    · intro he
      have hh := congrArg BitVec.toNat he
      have hl := hp.left.low
      change (16 * (count + 1)) % 2^64 = 16 at hh
      rw [Nat.mod_eq_of_lt (by omega : 16 * (count + 1) < 2^64)] at hh
      omega
    · intro hz
      subst count
      rfl
  rw [ha.rip]
  simp only [advanceEffect, heq, decide_eq_true_eq]

theorem scan [Bindings] (remaining : Nat) {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : ScanPre (remaining + 1) s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      AgreesExcept scanChanges s t ∧ ScanOutcome (remaining + 1) s t := by
  induction remaining using Nat.strongRecOn generalizing s with
  | ind remaining ih =>
    obtain ⟨n, u, hsu, hru, hcu, heu, hspu⟩ := chunk_branch boundary s hr hc hp.chunk hb
    have hfu := chunk_frame heu
    by_cases heq : BytesEqual s (leftAddress s) (rightAddress s) 16
    · have hipu := (chunk_branch_taken_iff heu).mpr heq
      obtain ⟨m, v, huv, hrv, hcv, hev, hspv⟩ :=
        loop_advance boundary u hru hcu hipu (hb.of_stack_eq hspu)
      have hfv := scan_frame_trans hfu (advance_frame hev)
      have hex : v.external = s.external := hfv.external (by simp [scanChanges, Component.Covers])
      obtain ⟨h8, h11, hl, hr'⟩ := scan_advance_values heu hev
      have hipv := scan_advance_rip hp heu hev
      by_cases hz : remaining = 0
      · refine ⟨n + m, v, hsu.trans huv, hrv, hcv, hfv, Or.inl ⟨?_, ?_⟩⟩
        · simpa only [hz, ite_true] using hipv
        · simpa only [hz] using heq
      · obtain ⟨rest, hrest⟩ := Nat.exists_eq_succ_of_ne_zero hz
        have hpv : ScanPre (rest + 1) v := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa only [hz, ite_false] using hipv
          · rw [h8, h11, hp.bound,
              show 16 * (remaining + 1) = 16 + 16 * (rest + 1) by omega,
              BitVec.ofNat_add, BitVec.add_assoc]
            rfl
          · rw [hl]
            exact (memReadable_slice hp.left 16 (16 * (rest + 1)) (by omega)).of_external_eq hex
          · rw [hr']
            exact (memReadable_slice hp.right 16 (16 * (rest + 1)) (by omega)).of_external_eq hex
        obtain ⟨k, t, hvt, hrt, hct, hft, hout⟩ :=
          ih rest (by omega) hrv hcv (hb.of_stack_eq (hspv.trans hspu)) hpv
        refine ⟨n + m + k, t, (hsu.trans huv).trans hvt, hrt, hct,
          scan_frame_trans hfv hft, ?_⟩
        have hlen : 16 * (remaining + 1) = 16 + 16 * (rest + 1) := by omega
        have hequiv : BytesEqual s (leftAddress s) (rightAddress s) (16 * (remaining + 1)) ↔
            BytesEqual v (leftAddress v) (rightAddress v) (16 * (rest + 1)) := by
          rw [hlen, bytesEqual_append]
          simp only [heq, true_and]
          simp only [hl, hr', BytesEqual, hex, BitVec.ofNat_eq_ofNat]
        rcases hout with hout | hout
        · exact Or.inl ⟨hout.1, hequiv.mpr hout.2⟩
        · exact Or.inr ⟨hout.1, fun hh ↦ hout.2.1 (hequiv.mp hh), hout.2.2⟩
    · have hipu : u.RIP = 0x11c8d0 := by
        rw [heu.rip]
        have hz : chunkDifference s ≠ 0 := fun hz ↦ heq ((chunkDifference_zero_iff s).mp hz)
        have hz' : chunkDifference s ≠ 0#64 := hz
        simp [chunkBranchEffect, hz']
      refine ⟨n, u, hsu, hru, hcu, hfu, Or.inr ⟨hipu, ?_, chunk_branch_mismatch heu hipu⟩⟩
      exact fun h ↦ heq (bytesEqual_prefix h (by omega))

end P256.Proofs.Program.Compare
