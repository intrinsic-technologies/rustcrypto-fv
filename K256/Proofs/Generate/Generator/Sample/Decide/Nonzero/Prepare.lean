import K256.Proofs.Generate.Generator.Sample.State
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def compareRegions (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 400).toNat, 8⟩, ⟨(fr.rsp - 352).toNat, 64⟩, ⟨(fr.rsp - 168).toNat, 32⟩]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 750000 in
theorem prepareCompare {s : RamState} {random : ByteArray} {fr : Activation} {i : Nat}
    {b : Registers} {mem : Ram} (decoded : AfterDecode s random fr i b mem) :
    ∃ c m, program.runBlock (dialect Extracted.programImage) ⟨.l105f70, b, mem⟩ =
      .call ⟨.l10a280, c, m⟩ ⟨.l105ff5, #v[], rfl, some ⟨64, 0x105ff5⟩⟩ ∧
      c[4] = ⟨64, fr.rsp - 400⟩ ∧ c[7] = ⟨64, fr.rsp - 320⟩ ∧ c[6] = ⟨64, fr.rsp - 168⟩ ∧
      ParseSignature.ArgumentWidths c ∧
      (∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15,22,39,50,51] → c[j] = b[j]) ∧
      RamWriteFrame mem m (compareRegions fr) ∧ memLoad m (fr.rsp - 400) 64 = 0x105ff5 ∧
      WordsAt m (fr.rsp - 352) 64 (Vector.ofFn fun j : Fin 4 => word s i j.val) ∧
      WordsAt m (fr.rsp - 320) 64 (Vector.ofFn fun j : Fin 4 => word s i j.val) ∧
      WordsAt m (fr.rsp - 168) 64 (Vector.replicate 4 0) := by
  obtain ⟨rsp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, win, room, _⟩ := decoded.atoms
  change Writable _ mem (fr.rsp - 10168) 10168 at win
  change fr.low.toNat + 10168 ≤ fr.rsp.toNat at room
  let sp := fr.rsp - 392
  have hsp : b[4].get 64 = sp := congrArg (Value.get 64) rsp
  have dst : b[15].get 64 = fr.rsp - 168 := congrArg (Value.get 64) decoded.decoded
  have window : Writable Extracted.programImage mem (sp - 8) 264 := by
    change Writable _ mem (fr.rsp - 392 - 8) _
    rw [show fr.rsp - 392 - 8 = fr.rsp - 400 by bv_omega]
    exact win.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have a0 : fr.rsp - 400 = sp - 8 := by dsimp only [sp]; bv_omega
  have a1 : fr.rsp - 352 = sp + 40 := by dsimp only [sp]; bv_omega
  have a2 : fr.rsp - 320 = sp + 72 := by dsimp only [sp]; bv_omega
  have a3 : fr.rsp - 168 = sp + 224 := by dsimp only [sp]; bv_omega
  rw [a3] at dst
  have inputs := decoded.limbs
  rw [a3] at inputs
  have w0 := inputs 0 (by decide)
  have w1 := inputs 1 (by decide)
  have w2 := inputs 2 (by decide)
  have w3 := inputs 3 (by decide)
  simp (config := { bitVecOfNat := false }) only [wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.reduceOfNat, Lift.reduceAddOffset, add_zero_lit, Vector.getElem_ofFn] at w0 w1 w2 w3
  rw [a0, a1, a2, a3]
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, dst]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105f70)
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ⟨j, hj⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact decoded.r8Width | exact decoded.r9Width
    · intro ⟨j, hj⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · unfold compareRegions
      rw [a0, a1, a3]
      slot_state region
    all_goals lifted_word_reads [w0, w1, w2, w3] <;> rfl

end K256.Proofs.Generate.Generator.Sample
