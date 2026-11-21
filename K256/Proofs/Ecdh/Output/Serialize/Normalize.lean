import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Generate.Generator.Affine.NormalizeCall
import K256.Proofs.Sec1.Serialize.Coordinates.Normalize

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Common.Field

private def canonicalArgs (a : Values Value Reg.count) : Values Value Reg.count :=
  Vector.ofFn fun i =>
    if i.val ∈ [5,12,13,15] then ⟨64, a[i].get 64⟩ else a[i]

private theorem canonicalNat (a : Values Value Reg.count) (i : Nat) (hi : i < Reg.count) :
    (canonicalArgs a)[i] = if i ∈ [5,12,13,15] then ⟨64, a[i].get 64⟩ else a[i] :=
  Vector.getElem_ofFn ..

private theorem normalizeBlock (a : Values Value Reg.count) (m : Ram) :
    program.runBlock (dialect Extracted.programImage) ⟨.l114930,a,m⟩ =
    program.runBlock (dialect Extracted.programImage) ⟨.l114930,canonicalArgs a,m⟩ := by
  cfg_eval
  simp (config := { decide := true }) only [canonicalNat, ↓reduceIte, Value.get_mk]

theorem normalize {a : Values Value Reg.count} {m : Ram} {base dst : Word} {w : Limbs}
    (rsp : a[4] = ⟨64,base - 8⟩) (rsi : a[6] = ⟨64,base + 8⟩) (rdi : a[7] = ⟨64,base + 48⟩)
    (rbx : a[3] = ⟨64,dst⟩) (r14 : a[14] = ⟨64,base + 48⟩) (df : a[22] = ⟨1,0⟩)
    (win : Writable Extracted.programImage m (base - 121) 433) (align : base.toNat % 16 = 0)
    (slot : memLoad m (base - 8) 64 = 0x120398) (input : WordsAt m (base + 8) 64 w) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l114930,a,m⟩,[]⟩ o ∧
      o.tag = some ⟨64,0x120398⟩ ∧ o.values[4] = ⟨64,base⟩ ∧
      o.values[3] = ⟨64,dst⟩ ∧ o.values[14] = ⟨64,base + 48⟩ ∧ o.values[22] = ⟨1,0⟩ ∧
      RamWriteFrame m o.store [⟨(base - 121).toNat,113⟩,⟨(base + 48).toNat,40⟩] ∧
      WordsAt o.store (base + 48) 64 (Sec1.Serialize.Normalize.normalize w) := by
  have same (i : Nat) (h : i ∉ [5,12,13,15]) (hi : i < Reg.count := by decide) :
      (canonicalArgs a)[i] = a[i] := by rw [canonicalNat, ite_eq_right h]
  have saved (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15]) :
      (canonicalArgs a)[i] = ⟨64, (canonicalArgs a)[i].get 64⟩ := by
    change (canonicalArgs a)[i.val] = ⟨64, (canonicalArgs a)[i.val].get 64⟩
    rw [canonicalNat]
    split
    · rw [Value.get_mk]
    · rename_i outside
      have cases : i.val = 3 ∨ i.val = 14 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h outside
        omega
      rcases cases with e|e
      · simp only [e, rbx, Value.get_mk]
      · simp only [e, r14, Value.get_mk]
  obtain ⟨hbase, hsp, off⟩ := Sec1.Serialize.Coordinates.stackOffsets win.readable.low
  have srcOff := off 8 (by decide)
  have dstOff := off 48 (by decide)
  change (base + 8).toNat = base.toNat + 8 at srcOff
  change (base + 48).toNat = base.toNat + 48 at dstOff
  have low : base - 8 - 113 = base - 121 := by bv_omega
  have stack : Writable Extracted.programImage m (base - 8 - 113) 121 := by
    rw [low]
    exact win.sub (Nat.le_refl _) (by omega)
  obtain ⟨o, run, tag, pop, keep, frame, words⟩ :=
    Generate.Generator.Affine.normalizeCall ((same 4 (by decide)).trans rsp)
      ((same 6 (by decide)).trans rsi) ((same 7 (by decide)).trans rdi)
      ((same 22 (by decide)).trans df) saved stack
      (win.readable.of_offsets rfl (addr_sub _ _) (by decide))
      (win.of_offsets rfl (addr_sub _ _) (by decide))
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      slot (by decide) input
  have child := Ecdh.Transfer.generateExec (dst := .l114930) (by decide) rfl run
  refine ⟨o, ?_, tag, ?_, (keep 3 (by decide)).trans ((same 3 (by decide)).trans rbx),
    (keep 14 (by decide)).trans ((same 14 (by decide)).trans r14),
    (keep 22 (by decide)).trans ((same 22 (by decide)).trans df), (by simpa only [low] using frame), words⟩
  · have stepEq : program.step (dialect Extracted.programImage) ⟨⟨.l114930,a,m⟩,[]⟩ =
        program.step (dialect Extracted.programImage) ⟨⟨.l114930,canonicalArgs a,m⟩,[]⟩ :=
      congrArg (fun block => block.next (dialect Extracted.programImage) []) (normalizeBlock a m)
    cases child with
    | done h => exact .done (stepEq.trans h)
    | next h tail => exact .next (stepEq.trans h) tail
  · simpa only [BitVec.sub_add_cancel] using pop

end K256.Proofs.Ecdh.Output
