import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Compose
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Entry
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Finish
import K256.Proofs.Common.Point.DoubleWords.ReplayCorrect.Output

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open Common.Point Common.Field DoubleReplay

theorem doubleArithmetic_of_segments
    (segments : ∀ {a : Registers} {p : PointWords} {yy zz : Limbs}
      {sp : Word} {count : BitVec 32}, a[4] = ⟨64, sp⟩ → a[5] = ⟨64, 0x1000003d10⟩ →
        Segment a p yy zz sp count b_l11d880 b_l11d880_83) :
    DoubleArithmetic := by
  intro fr p a m n x y z hn
  dsimp only
  intro atoms rbp counter saved wx wy wz copies zs hx hy hz
  let sp := fr.rsp - 0xcb8
  let raw : PointWords := ⟨x, y, z⟩
  let yy := squareWords y
  let zz := squareWords z
  have access : a[4] = ⟨64, sp⟩ ∧ Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8 ∧
      0xed8 ≤ fr.rsp.toNat ∧ fr.rsp.toNat + 8 ≤ 2^32 := by
    obtain ⟨rsp, _, _, _, _, _, _, _, _, _, _, retRead, _, _, window, depth, _⟩ := atoms
    change fr.low.toNat + 0xed8 ≤ fr.rsp.toNat at depth
    exact ⟨rsp, window, by omega, (show Readable m fr.rsp 8 from retRead).low⟩
  obtain ⟨rsp, window, depth, top⟩ := access
  have win : Writable Extracted.programImage m sp 0x878 :=
    window.of_offsets (x := fr.rsp) (c := -0xcb8) (d := -0xed8)
      (by dsimp only [sp]; bv_omega) (by bv_omega) (by decide)
  have start : ValuesMatch (values a raw yy zz sp) a := by
    intro i
    have hi : i.val < 53 := i.isLt
    simp only [values, hi, dite_true, Fin.getElem_fin]
  have mem := DoubleReplay.entryMemory (p := raw) win wx wy wz copies zs counter saved
  obtain ⟨scope, scratch, step, regValues, memory, frame⟩ :=
    segments (p := raw) (yy := yy) (zz := zz) (count := BitVec.ofNat 32 (n+1)) rsp rbp start mem
  obtain ⟨b, out, last, count, keep, widths, savedW, mask, temp, newX, newY, newZ, lastFrame⟩ :=
    finishReplay rsp regValues memory hn
  have frame' := frame.trans lastFrame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have labels := body_frame atoms keep frame'
  have outAtoms : Atom.All Extracted.programImage b out (Fn11c880.frameAt (doublesLabel n) fr) := by
    by_cases h : n = 0
    · simpa only [doublesLabel, h, ite_true] using labels.2
    · simpa only [doublesLabel, h, ite_false] using labels.1
  have preserveMask : memLoad out (sp + 0x1c8) 64 = 0xfffffffffff8 := by
    have hs : sp.toNat = fr.rsp.toNat - 0xcb8 :=
      BitVec.toNat_sub_of_le (Nat.le_trans (by decide : 0xcb8 ≤ 0xed8) depth)
    have haddr : (sp + 0x1c8).toNat = fr.rsp.toNat - 0xcb8 + 0x1c8 := by
      rw [BitVec.toNat_add, hs]
      change (fr.rsp.toNat - 0xcb8 + 0x1c8) % 2^64 = _
      exact Nat.mod_eq_of_lt (by omega)
    exact (frame'.memLoad_eq (body_outside (fr := fr) depth top
      (by rw [haddr]; omega) (by rw [haddr]; omega))).trans saved
  have outFrame : RamWriteFrame m out (doubleWrites sp) := by
    apply (RamWriteFrame.refl m (doubleWrites sp)).trans frame'
    intro r hr
    refine ⟨r, ?_, Nat.le_refl _, Nat.le_refl _⟩
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [doubleWrites]
  have words := Common.Point.DoubleWords.Replay.output_eq raw sp hx hy hz
  change Common.Point.DoubleWords.Replay.output raw yy zz sp = _ at words
  rw [words] at newX newY newZ
  have acc : p.double.Stored out (fr.rsp - 0xb90) := by
    let result := Common.Point.DoubleWords.double raw
    refine ⟨result.x, result.y, result.z, ?_, ?_, ?_,
      Common.Point.DoubleWords.double_repr (words := raw) (p := p) hx hy hz⟩
    · rw [show fr.rsp - 0xb90 = sp + 0x128 by dsimp only [sp]; bv_omega]
      exact newX
    · rw [show fr.rsp - 0xb90 + 40 = sp + 0x150 by dsimp only [sp]; bv_omega]
      exact newY
    · rw [show fr.rsp - 0xb90 + 80 = sp + 0x178 by dsimp only [sp]; bv_omega]
      exact newZ
  refine ⟨b, out, ?_, ⟨outAtoms, widths, savedW, count, mask, temp, preserveMask, acc⟩, outFrame⟩
  have run : program.runBlock (dialect Extracted.programImage) ⟨.l11d880, a, m⟩ =
      .jump ⟨doublesLabel n, b, out⟩ := step.trans last
  refine .step (b := ⟨⟨doublesLabel n, b, out⟩, []⟩) ?_ (Star.refl _)
  simp only [Program.sem, Program.step, run, Transfer.next]

end K256.Proofs.Generate.Generator.Multiply
