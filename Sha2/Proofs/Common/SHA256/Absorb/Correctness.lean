import Sha2.Proofs.Common.SHA256.Absorb.Proof.Small
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Branch
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Empty
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Fill
import Sha2.Proofs.Common.SHA256.Absorb.Proof.SelectBlocks
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Bulk

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] (l : Layout) : Contract l := by
  intro initial s n reserve regions prior input wf flow code targets blocks stride machine stack
    avoids returnAddress state data apart within
  let ctx : Context l initial regions reserve :=
    ⟨wf, flow, code, targets, blocks, stride, machine, stack, avoids, returnAddress, within⟩
  obtain ⟨u, preserved, prepared, count, remaining, rip⟩ := select_size ctx state data
  by_cases short : input.bytes.size < 64 - prior.size % 64
  · exact small ctx preserved prepared (by simpa only [short, ite_true] using rip) short apart
  · have large : 64 - prior.size % 64 ≤ input.bytes.size := by omega
    obtain ⟨v, stateV, dataV, branch, agrees⟩ := select_empty ctx preserved prepared
      (by simpa only [short, ite_false] using rip)
    have buffer {t : RamState} (kept : Preserved l initial s t regions) :
        ∀ r ∈ l.bufferSource, Blocks.readReg t r = l.buffer (l.sp initial) :=
      kept.buffer_register flow data.bufferRegister
    have copies {t : RamState} (kept : Preserved l initial s t regions) :
        ∀ r, l.tailCall.encoding = .register r → Blocks.readReg t r = 0x10dd60 :=
      kept.copy_register targets (by simp) (data.copyRegister l.tailCall (by simp))
    have bytes {t : RamState} (kept : Preserved l initial s t regions) :
        input.region.HasBytes t.external input.bytes :=
      ctx.input_bytes data.bytes data.bounded apart kept.frame
    by_cases empty : prior.size % 64 = 0
    · obtain ⟨w, stateW, aligned, setup, restored, countW⟩ := empty_setup ctx stateV dataV
        (by simpa only [empty, ite_true] using branch) empty
      have lengthV : Blocks.readReg v l.registers.length = BitVec.ofNat 64 input.bytes.size := dataV.length
      have shifted : Blocks.readReg v l.registers.length >>> 6 = BitVec.ofNat 64 (input.bytes.size / 64) := by
        rw [lengthV, Wrapper.Absorb.block_count, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := data.messageBound; omega)]
      have zeroIff : BitVec.ofNat 64 (input.bytes.size / 64) = 0 ↔ input.bytes.size / 64 = 0 := by
        constructor
        · intro h
          have same := congrArg BitVec.toNat h
          simpa only [BitVec.toNat_ofNat, BitVec.reduceToNat,
            Nat.mod_eq_of_lt (by have := data.messageBound; omega : input.bytes.size / 64 < 2^64)] using same
        · intro h
          rw [h]
          rfl
      have pc : w.RIP = if (input.bytes.size - 0) / 64 = 0 then l.pc .splitTail else l.pc .addBlocks := by
        rw [setup.rip]
        change (if Blocks.readReg v l.registers.length >>> 6 = 0 then _ else _) = _
        simp only [shifted, zeroIff, Nat.sub_zero]
      exact bulk_tail ctx stateW aligned pc (by simpa only [Nat.sub_zero] using countW)
        large data.messageBound (bytes stateW) data.bounded apart (buffer stateW) restored (copies stateW)
    · have countV : v.regValue .rdx = BitVec.ofNat 64 (64 - prior.size % 64) :=
        (agrees.read (n := 64) (r := 2) (by simp)).trans count
      have remainingV : Blocks.readReg v l.registers.remaining =
          BitVec.ofNat 64 (input.bytes.size - (64 - prior.size % 64)) := by
        apply Eq.trans (agrees.read (by simp))
        change Blocks.readReg u l.registers.remaining = _
        rw [remaining]
        exact BitVec.ofNat_sub_ofNat_of_le (w := 64) input.bytes.size (64 - prior.size % 64) (by have := data.messageBound; omega) large
      obtain ⟨w, stateW, aligned, pcW, restoredW⟩ := fill ctx stateV dataV
        (by simpa only [empty, ite_false] using branch) large countV remainingV apart
      obtain ⟨x, stateX, alignedX, pcX, countX, restoredX, _⟩ := select_blocks ctx stateW aligned
        (by have := data.messageBound; omega) pcW (buffer stateW) restoredW
      exact bulk_tail ctx stateX alignedX pcX countX large data.messageBound
        (bytes stateX) data.bounded apart (buffer stateX) restoredX (copies stateX)

end Sha2.Proofs.Common.SHA256.Absorb
