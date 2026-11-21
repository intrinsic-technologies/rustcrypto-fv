import P256.Proofs.Program.Compare.Chunk
import P256.Proofs.Program.Compare.Bytes
import X86Proofs.Instructions.Branch.Triple

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

private theorem chunk_avoids (s : RamState) (code : CodeMap) : (chunkEffect s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [chunkEffect, Effect.components, Component.Covers]) code

theorem chunk_code {s : RamState} (h : CodeIn Extracted.programSections.toCodeMap s) :
    CodeIn (codeRange 0x11c890 chunkBytes) s := by
  have hs := program_text_slice h 0x1c890 33 (by decide +kernel)
  have he : Extracted.textBytes.toListFrom 0x1c890 33 = chunkBytes := by decide +kernel
  simpa [he, Extracted.textAddress] using hs

theorem chunk_compare_program [Bindings] : RegisterBlock ChunkPre Extracted.programSections.toCodeMap
    chunkEffect := by
  intro boundary s hr hc hp hb
  obtain ⟨n, t, ha, ht, _, he, hsp⟩ := chunk_compare boundary s hr (chunk_code hc) hp hb
  exact ⟨n, t, ha, ht, he.codeIn (chunk_avoids s _) hc, he, hsp⟩

def chunkBranchEffect (s : RamState) : Effect :=
  { chunkEffect s with rip := if chunkDifference s == 0 then 0x11c8b3 else 0x11c8d0 }

theorem chunk_branch [Bindings] : RegisterBlock ChunkPre Extracted.programSections.toCodeMap
    chunkBranchEffect := by
  intro boundary s hr hc hp hb
  obtain ⟨n, u, ha, hu, hcu, he, hsp⟩ := chunk_compare_program boundary s hr hc hp hb
  have hjcode : CodeIn (codeRange 0x11c8b1 [0x75, 0x1d]) u :=
    program_text_slice hcu 0x1c8b1 2 (by decide +kernel)
  obtain ⟨t, hstep, ht, hj⟩ := jcc_rel8_effect_step 0x11c8b1 5 0x1d u hu hjcode
    ⟨he.rip, fun _ ↦ by decide +kernel⟩
  have hreads (r : BitVec 5) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u :=
    hj.agrees.read (by simp [jccEffect, branchEffect, Effect.components])
  have hsp' : stackPtr t = stackPtr u := hreads 4
  have hip : InRoutine t.RIP := by
    rw [hj.rip]
    unfold jccEffect branchEffect
    split <;> constructor <;> decide +kernel
  have haj := (hb.of_stack_eq hsp).advances hstep hsp' hip
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (chunkDifference s == 0) := he.flags.2.2.2.1
  have hrt : t.RIP = (chunkBranchEffect s).rip := by
    rw [hj.rip]
    simp only [jccEffect, branchEffect, condHolds, hz,
      chunkBranchEffect]
    cases (chunkDifference s == 0) <;> rfl
  have hflags := hj.agrees.rflags (by simp [jccEffect, branchEffect, Effect.components]) (by simp [jccEffect, branchEffect, Effect.components])
  refine ⟨n + 1, t, ha.trans haj, ht,
    hj.codeIn (branchEffect_avoids _ _ _ _) hcu, ?_, hsp'.trans hsp⟩
  refine ⟨hrt, ?_, ?_, ?_⟩
  · simpa only [chunkBranchEffect, chunkEffect, Write.AllHold, hreads] using he.writes
  · simpa only [chunkBranchEffect, chunkEffect, Effect.FlagsHold, hflags] using he.flags
  · apply (he.agrees.trans hj.agrees).mono
    simp [chunkEffect, chunkBranchEffect, jccEffect, branchEffect, Effect.components]

theorem chunk_branch_taken_iff {s t : RamState} (h : (chunkBranchEffect s).Holds s t) :
    t.RIP = 0x11c8b3 ↔ BytesEqual s (leftAddress s) (rightAddress s) 16 := by
  rw [h.rip, ← chunkDifference_zero_iff]
  simp [chunkBranchEffect]

theorem chunk_branch_mismatch {s t : RamState} (h : (chunkBranchEffect s).Holds s t)
    (hip : t.RIP = 0x11c8d0) :
    (Operand.reg 0 : Operand 64).read t ≠ (Operand.reg 7 : Operand 64).read t ∨
      (Operand.reg 3 : Operand 64).read t ≠ (Operand.reg 14 : Operand 64).read t := by
  have hne : chunkDifference s ≠ 0 := by
    intro he
    have hz : t.RIP = 0x11c8b3 := (chunk_branch_taken_iff h).mpr ((chunkDifference_zero_iff s).mp he)
    have hh : (0x11c8d0 : BitVec 64) ≠ 0x11c8b3 := by decide +kernel
    exact hh (hip.symm.trans hz)
  rw [h.writes.1, h.writes.2.2.1, h.writes.2.1, h.writes.2.2.2.1]
  by_cases he : leftWord s 0 = rightWord s 0
  · right
    intro hh
    apply hne
    have he' : leftWord s 0#64 = rightWord s 0#64 := by simpa only [BitVec.ofNat_eq_ofNat] using he
    have hh' : leftWord s 8#64 = rightWord s 8#64 := by simpa only [BitVec.ofNat_eq_ofNat] using hh
    simp [chunkDifference, he', hh']
  · exact Or.inl he

end P256.Proofs.Program.Compare
