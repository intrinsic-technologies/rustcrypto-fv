import K256.Proofs.Verify.Core.Serializer

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private abbrev normalizeSerializer (a : Registers) : Registers :=
  (((a.set 1 ⟨64, 0⟩).set 2 ⟨64, 0⟩).set 8 ⟨64, 0⟩).set 9 ⟨64, 0⟩

private abbrev restoreSerializer (a : Registers) (out : Output Value Ram Reg.count) :
    Output Value Ram Reg.count :=
  { out with values := (out.values.set 8 a[8]).set 9 a[9] }

private def restoreSerializerTransfer (a : Registers)
    (tr : Transfer Value Ram Label signature Reg.count) :
    Transfer Value Ram Label signature Reg.count :=
  match tr with
  | .returned out => .returned (restoreSerializer a out)
  | t => t

private theorem restoreSerializerIte (a : Registers) {c : Prop} [Decidable c]
    (tr : Transfer Value Ram Label signature Reg.count) :
    restoreSerializerTransfer a (if c then tr else .stuck) =
      if c then restoreSerializerTransfer a tr else .stuck := by
  split <;> rfl

set_option maxRecDepth 1600 in
set_option maxHeartbeats 800000 in
private theorem restoreSerializerRun (a : Registers) (m : Ram) :
    program.runBlock (dialect Extracted.programImage) ⟨.l10a2f0, a, m⟩ =
      restoreSerializerTransfer a
        (program.runBlock (dialect Extracted.programImage) ⟨.l10a2f0, normalizeSerializer a, m⟩) := by
  rw [serializerBlock, serializerBlock]
  dsimp only
  simp (config := { decide := true }) only [normalizeSerializer, Vector.getElem_set,
    ↓reduceIte, restoreSerializerIte]
  congr 40

private def serializerContinues : Transfer Value Ram Label signature Reg.count → Bool
  | .jump _ | .call _ _ => true
  | _ => false

private theorem serializerContinuesIte {c : Prop} [Decidable c]
    (tr : Transfer Value Ram Label signature Reg.count) :
    serializerContinues (if c then tr else .stuck) =
      if c then serializerContinues tr else false := by
  split <;> rfl

set_option maxRecDepth 1600 in
private theorem serializerTerminal (a : Registers) (m : Ram) :
    serializerContinues (program.runBlock (dialect Extracted.programImage) ⟨.l10a2f0, a, m⟩) = false := by
  rw [serializerBlock]
  dsimp only
  simp only [serializerContinuesIte,
    show ∀ out, serializerContinues (.returned out) = false from fun _ => rfl, ite_self]

private theorem valueEq (v : Value) {w : Nat} (h : v.width = w) :
    v = ⟨w, v.get w⟩ := by
  cases v
  subst w
  simp only [Value.get_mk]

private def serializerActivation (a : Registers) (m : Ram) (sp ret src dst : BitVec 64) :
    Activation where
  original := m
  rsp := sp
  ret := ret
  low := sp
  rbx := a[3].get 64
  rbp := a[5].get 64
  r12 := a[12].get 64
  r13 := a[13].get 64
  r14 := a[14].get 64
  r15 := a[15].get 64
  rdi := dst
  rsi := src
  rcx := 0
  rdx := 0
  r8 := 0
  r9 := 0
  mxcsr := a[39].get 32
  ftw := a[50].get 16
  fcw := a[51].get 16
  fs := default

set_option maxRecDepth 1600 in
set_option maxHeartbeats 800000 in
theorem serializeForDigits {a : Registers} {m : Ram} {sp ret src dst : BitVec 64}
    {w : Vector (BitVec 64) 4}
    (rsp : a[4] = ⟨64, sp⟩) (si : a[6] = ⟨64, src⟩) (di : a[7] = ⟨64, dst⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64)
    (df : a[22] = ⟨1, 0⟩) (mx : a[39].width = 32) (ft : a[50].width = 16)
    (fc : a[51].width = 16) (aligned : sp.toNat % 16 = 8)
    (retRead : Readable m sp 8) (retValue : memLoad m sp 64 = ret) (low : ret.toNat < 2^32)
    (srcRead : Readable m src 32) (dstWrite : Writable Extracted.programImage m dst 32)
    (words : WordsAt m src 64 w)
    (separate : dst.toNat + 32 ≤ src.toNat ∨ src.toNat + 32 ≤ dst.toNat)
    (retApart : dst.toNat + 32 ≤ sp.toNat ∨ sp.toNat + 8 ≤ dst.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a2f0, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [⟨dst.toNat, 32⟩] ∧ WordsAt out.store dst 64 w := by
  let fr := serializerActivation a m sp ret src dst
  have atoms : Atom.All Extracted.programImage (normalizeSerializer a) m (Fn10a2f0.frameAt .l10a2f0 fr) := by
    simp (config := { decide := true }) only [Fn10a2f0.frameAt, Fn10a2f0.frameAtG12, Atom.All, Atom.Holds,
      fr, serializerActivation, normalizeSerializer, Fin.getElem_fin, Vector.getElem_set, ↓reduceIte]
    exact ⟨rsp, df, trivial, trivial, valueEq _ (widths 3 (by decide)), valueEq _ (widths 5 (by decide)),
      si, di, trivial, trivial, valueEq _ (widths 12 (by decide)), valueEq _ (widths 13 (by decide)),
      valueEq _ (widths 14 (by decide)), valueEq _ (widths 15 (by decide)),
      valueEq _ mx, valueEq _ ft, valueEq _ fc, retRead, retValue, low, Nat.le_refl _, aligned, trivial⟩
  obtain ⟨out, exec, tag, _, done, frame, saved⟩ :=
    serializeScalar atoms srcRead dstWrite words separate retApart
  have run : program.runBlock (dialect Extracted.programImage)
      ⟨.l10a2f0, normalizeSerializer a, m⟩ = .returned out := by
    generalize he : program.runBlock (dialect Extracted.programImage)
        ⟨.l10a2f0, normalizeSerializer a, m⟩ = tr
    have step : program.step (dialect Extracted.programImage)
        ⟨⟨.l10a2f0, normalizeSerializer a, m⟩, []⟩ = Transfer.next (dialect Extracted.programImage) [] tr := by
      simp only [Program.step, he]
    cases exec with
    | done h =>
      rw [step] at h
      cases tr <;> simp only [Transfer.next, reduceCtorEq, Outcome.done.injEq] at h ⊢
      exact congrArg Transfer.returned h
    | next h _ =>
      rw [step] at h
      cases tr <;> simp only [Transfer.next, reduceCtorEq] at h
      all_goals
        have terminal := serializerTerminal (normalizeSerializer a) m
        rw [he] at terminal
        contradiction
  have run' : program.runBlock (dialect Extracted.programImage) ⟨.l10a2f0, a, m⟩ =
      .returned (restoreSerializer a out) := by rw [restoreSerializerRun, run]; rfl
  obtain ⟨outSp, outDf, outBx, outBp, out12, out13, out14, out15, outMx, outFt, outFc, _⟩ := done
  refine ⟨restoreSerializer a out, .done (by simp only [Program.step, run', Transfer.next]), tag, ?_, ?_, frame, saved⟩
  · simpa (config := { decide := true }) only [restoreSerializer, Fin.getElem_fin, Vector.getElem_set, ↓reduceIte] using (show out.values[4] = ⟨64, sp + 8⟩ from outSp)
  · intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp (config := { decide := true }) only [Fin.getElem_fin, Vector.getElem_set, ↓reduceIte]
    · exact outBx.trans (valueEq _ (widths 3 (by decide))).symm
    · exact outBp.trans (valueEq _ (widths 5 (by decide))).symm
    · exact out12.trans (valueEq _ (widths 12 (by decide))).symm
    · exact out13.trans (valueEq _ (widths 13 (by decide))).symm
    · exact out14.trans (valueEq _ (widths 14 (by decide))).symm
    · exact out15.trans (valueEq _ (widths 15 (by decide))).symm
    · exact outDf.trans df.symm
    · exact outMx.trans (valueEq _ mx).symm
    · exact outFt.trans (valueEq _ ft).symm
    · exact outFc.trans (valueEq _ fc).symm

end K256.Proofs.Verify.Core.Lincomb.Prepare
