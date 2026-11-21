import K256.Proofs.Signing.Affine.State
import K256.Proofs.Generate.Generator.Affine.Select.Setup
import K256.Proofs.Generate.LIR.Fn10fe50
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Affine

open K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

private def identityBytes := List.ofFn fun i : Fin 88 => if i.val = 80 then (1 : UInt8) else 0

set_option maxRecDepth 4096 in
private theorem identityCode : ∀ x ∈ codeRange 0x202b70 identityBytes, x ∈ Extracted.programImage := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  exact codeRange_sub_section (s := sec)
    (by simp [sec, Extracted.programSections]) 0x2b70 88 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl

private theorem identitySource {m : Ram} {dst : Word}
    (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (w : Writable Extracted.programImage m dst 88) :
    Readable m 0x202b70 88 ∧ (0x202bc8 ≤ dst.toNat ∨ dst.toNat + 88 ≤ 0x202b70) := by
  apply readableCodeSpan (code := Extracted.programImage) _ loaded (by decide) (by decide) w (by decide)
  intro i hi
  have h : i < identityBytes.length := by simpa only [identityBytes, List.length_ofFn] using hi
  exact ⟨_, identityCode _ (mem_codeRange 0x202b70 identityBytes i h)⟩

theorem setupSelection {fr : Activation} {a : Registers} {m : Ram} {point : Curve.Point}
    (s : CallState .l10ee37 fr a m) (h : Products fr a m point) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10ee37, a, m⟩ =
      .call ⟨.l120470, b, setupMemory fr m⟩ (K256.Proofs.Generate.Generator.callFrame .l10ee65 0x10ee65) ∧
      SelectionArguments fr a b ∧ RamWriteFrame m (setupMemory fr m) (setupWrites fr) := by
  have atoms : Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10ee37 fr) := s.atoms
  simp only [Fn10fe50.frameAt, Fn10fe50.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, rdi, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, lower, _, _⟩ := atoms
  have sp : a[4].get 64 = fr.rsp - 232 := congrArg (Value.get 64) rsp
  have direction : a[22].get 1 = 0 := congrArg (Value.get 1) df
  have bx : a[3].get 64 = fr.rdi := congrArg (Value.get 64) rdi
  have arg : a[12].get 64 = fr.rsp - 144 := congrArg (Value.get 64) h.address
  have choice : a[15].get 64 = 1 := congrArg (Value.get 64) h.choice
  let flag := memStore m (fr.rsp - 56) (1 : BitVec 8)
  let copied := memCopy flag (fr.rsp - 232) 0x202b70 88
  have writable (k : BitVec 64) (n : Nat) (fit : (0 - k - (0 - 976) : BitVec 64).toNat + n ≤ 976) :
      Writable Extracted.programImage m (fr.rsp - k) n :=
    stack.of_offsets (addr_sub _ _) (addr_sub _ _) fit
  have flagOk : StoreOk Extracted.programImage m (fr.rsp - 56) 1 0x10ee37 8 :=
    by slot_guard using code_l10ee37
  obtain ⟨source, apart⟩ := identitySource s.image (writable 232 88 (by decide))
  have copyStore : StoreOk Extracted.programImage flag (fr.rsp - 232) 88 0x10ee51 3 :=
    by
      change StoreOk _ (memStore m (fr.rsp - 56) (1 : BitVec 8)) _ _ _ _
      slot_guard using code_l10ee37
  have copyOk : RepMovsOk Extracted.programImage flag 0 0x202b70 (fr.rsp - 232) 11 8 0x10ee51 3 :=
    ⟨rfl, source.low, copyStore.low, (source.memStore _ (1 : BitVec 8)).present, copyStore.present, apart,
      copyStore.tables, copyStore.apart, copyStore.notCode⟩
  have pushOk : StoreOk Extracted.programImage copied (fr.rsp - 240) 8 0x10ee60 5 := by
    change StoreOk _ (memStore (memStore m (fr.rsp - 56) (1 : BitVec 8))
      (fr.rsp - 232) (memLoad flag 0x202b70 704)) _ _ _ _
    slot_guard using code_l10ee37
  have flagAddr : fr.rsp - 232 + 176 = fr.rsp - 56 := by bv_omega
  have pushAddr : fr.rsp - 232 - 8 = fr.rsp - 240 := by bv_omega
  refine ⟨?b, ?run, ?args, ?frame⟩
  case run =>
    cfg_eval [sp, direction, bx, arg, choice, flagAddr, pushAddr, flagOk]
    change (if False ∨ RepMovsOk _ flag _ _ _ _ _ _ _ then
      if StoreOk _ copied _ _ _ _ then _ else _ else _) = _
    rw [ite_eq_left (Or.inr copyOk), ite_eq_left pushOk]
    rfl
  case args =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame =>
    change RamWriteFrame m
      (memStore (memStore (memStore m (fr.rsp - 56) (1 : BitVec 8)) (fr.rsp - 232)
        (memLoad flag 0x202b70 704)) (fr.rsp - 240) (0x10ee65 : Word)) (setupWrites fr)
    unfold setupWrites
    have bound := stack.readable.low
    have nat976 : (fr.rsp - 976).toNat = fr.rsp.toNat - 976 := stackBaseNat lower (by decide)
    have nat56 : (fr.rsp - 56).toNat = fr.rsp.toNat - 56 := stackBaseNat lower (by decide)
    have nat240 : (fr.rsp - 240).toNat = fr.rsp.toNat - 240 := stackBaseNat lower (by decide)
    have nat232 : (fr.rsp - 232).toNat = fr.rsp.toNat - 232 := stackBaseNat lower (by decide)
    rw [nat976] at bound
    slot_state region

end K256.Proofs.Signing.Affine
