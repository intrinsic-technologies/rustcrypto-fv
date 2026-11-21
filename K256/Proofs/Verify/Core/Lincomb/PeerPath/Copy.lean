import K256.Proofs.Verify.Core.Lincomb.PeerPath.State
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.Core.Lincomb.PeerPath.CopySetup

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

private theorem afterCopy {d x f : Registers} {n t : Ram} {dst len : Nat}
    (e : Entry fr a p digest r s) (saved : CallerFrame fr c d m n)
    (lo : 8 ≤ dst) (hi : dst + len ≤ 0x28a8)
    (frame : RamWriteFrame n t (workWrites fr 8 dst len))
    (sp : f[4] = ⟨64, workSp fr⟩) (r12 : f[12].width = 64)
    (setup : ∀ j : Fin Reg.count, j.val ∈ [3,5,13,14,15,22,39,50,51] → x[j] = d[j])
    (kept : ∀ j : Fin Reg.count, j.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → f[j] = x[j]) :
    CallerFrame fr c f m t ∧
      ∀ j : Fin Reg.count, j.val ∈ [3,5,13,14,15,22,39,50,51] → f[j] = d[j] := by
  have eq (j : Fin Reg.count) (hj : j.val ∈ [3,5,13,14,15,22,39,50,51]) : f[j] = d[j] :=
    (kept j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)).trans (setup j hj)
  refine ⟨CallerFrame.next e saved (by decide) lo hi frame sp ?_ ?_, eq⟩
  · intro j hj
    by_cases h12 : j.val = 12
    · obtain rfl : j = 12 := Fin.ext h12
      exact r12
    · rw [eq j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]
      exact saved.widths j hj
  · intro j hj
    exact eq j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)

theorem copyGenerator (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) {d n}
    (saved : CallerFrame fr c d m n) (generator : GeneratorPrepared fr d n u) :
    ∃ f t, Reaches .l10fba8 d n .l10fbd5 f t ∧ CallerFrame fr c f m t ∧
      GeneratorCopy fr t u ∧ PreparesPeer fr f 0x1568 := by
  have whole := h.frame.trans saved.frame (frameBounds e).1
  have push := belowWrite e whole (depth := 8) (by decide)
  have guard₁ : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fbbf 3 :=
    ParseSignature.storeOk_of_codeRange (off := 23) push
      (fun x hx => Common.fnCode_subset_programImage x (code_l10fba8 x hx)) (by decide)
  have tableAddr : d[5].get 64 = slot fr 0x1568 := by rw [generator.tablePtr]; rfl
  obtain ⟨x, call₁, sp₁, dst₁, src₁, len₁, ptr₁, setup₁⟩ := tableCopySetup (fr := fr) (d := d)
    (by rw [saved.sp]; rfl) tableAddr guard₁
  have df : d[22] = ⟨1, 0⟩ :=
    (saved.fixedRegs 22 (by decide)).trans ((args.keep 22 (by decide)).trans h.df)
  obtain ⟨d₁, n₁, run₁, rsp₁, keep₁, copy₁, frame₁⟩ :=
    copyCall (ret := 0x10fbc2) (src := 0x1568) (dst := 0xbc8) (len := 1920) e whole (by decide) (by decide)
      (by decide) (by decide) call₁ sp₁ dst₁ src₁ len₁ (congrArg (Value.get 1) ((setup₁ 22 (by decide)).trans df))
  have memcpy₁ := (keep₁ 12 (by decide)).trans ptr₁
  obtain ⟨saved₁, regs₁⟩ := afterCopy e saved (by decide) (by decide) frame₁ rsp₁
    (congrArg Value.width memcpy₁) setup₁ keep₁
  have whole₁ := h.frame.trans saved₁.frame (frameBounds e).1
  have guard₂ : StoreOk Extracted.programImage n₁ (workSp fr - 8) 8 0x10fbd2 3 :=
    ParseSignature.storeOk_of_codeRange (off := 16) (belowWrite e whole₁ (depth := 8) (by decide))
      (fun x hx => Common.fnCode_subset_programImage x (code_l10fbc2 x hx)) (by decide)
  have digitAddr : d₁[13] = ⟨64, slot fr 0x228⟩ := (regs₁ 13 (by decide)).trans generator.digitsPtr
  obtain ⟨y, call₂, sp₂, dst₂, src₂, len₂, ptr₂, setup₂⟩ := digitCopySetup (fr := fr) (d := d₁)
    (by rw [rsp₁]; rfl)
    (by rw [digitAddr]; rfl)
    (congrArg (Value.get 64) memcpy₁) guard₂
  obtain ⟨f, t, run₂, rsp₂, keep₂, copy₂, frame₂⟩ :=
    copyCall (ret := 0x10fbd5) (src := 0x228) (dst := 0x1348) (len := 544) e whole₁ (by decide) (by decide)
      (by decide) (by decide) call₂ sp₂ dst₂ src₂ len₂
      (congrArg (Value.get 1) ((setup₂ 22 (by decide)).trans ((regs₁ 22 (by decide)).trans df)))
  have memcpy₂ := ((keep₂ 12 (by decide)).trans ptr₂).trans memcpy₁
  obtain ⟨saved₂, regs₂⟩ := afterCopy e saved₁ (by decide) (by decide) frame₂ rsp₂
    (congrArg Value.width memcpy₂) setup₂ keep₂
  have gen₁ := generator.prepared.of_copy copy₁
    (Copied.of_frame frame₁ (workOutside e (by decide) (by decide) (by decide) (by decide)))
  have gen₂ := gen₁.of_copy
    (Copied.of_frame frame₂ (workOutside e (by decide) (by decide) (by decide) (by decide))) copy₂
  exact ⟨f, t, run₁.trans run₂, saved₂, gen₂,
    (regs₂ 3 (by decide)).trans ((regs₁ 3 (by decide)).trans generator.memset), memcpy₂,
    (regs₂ 14 (by decide)).trans ((regs₁ 14 (by decide)).trans generator.scalar),
    (regs₂ 15 (by decide)).trans ((regs₁ 15 (by decide)).trans generator.key),
    (regs₂ 5 (by decide)).trans ((regs₁ 5 (by decide)).trans generator.tablePtr)⟩

end K256.Proofs.Verify.Core.Lincomb
