import K256.Proofs.Generate.Generator.Multiply.Constants
import K256.Proofs.Generate.Generator.Affine.Select.Setup

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.Lift K256.Proofs.Refine Generate.Generator.Multiply

private def identityBytes := List.ofFn fun i : Fin 120 => if i.val = 40 then (1 : UInt8) else 0

set_option maxRecDepth 4096 in
private theorem identityCode {base : BitVec 64} (addr : base = 0x202d48 ∨ base = 0x202c40) :
    ∀ x ∈ codeRange base identityBytes, x ∈ Extracted.programImage := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have mem : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  rcases addr with rfl | rfl
  · exact codeRange_sub_section mem 0x2d48 120 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl
  · exact codeRange_sub_section mem 0x2c40 120 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl

theorem identityImage {m : Ram} (loaded : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2) :
    identity.Stored m 0x202d48 := by
  apply (identity_stored loaded (Or.inl rfl)).of_word_copy
  intro i
  apply memLoad_congr
  intro j hj
  have bound : 8*i.val + j < identityBytes.length := by
    simp only [identityBytes, List.length_ofFn]
    have := i.isLt
    change j < 8 at hj
    omega
  have byte (base : BitVec 64) (addr : base = 0x202d48 ∨ base = 0x202c40) :=
    loaded _ (identityCode addr _ (mem_codeRange base identityBytes _ bound))
  simp only [wordAddr, Nat.reduceDiv, BitVec.add_assoc, ← BitVec.ofNat_add, memByte]
  exact congrArg (fun v : Option UInt8 => v.getD 0) ((byte _ (Or.inl rfl)).trans (byte _ (Or.inr rfl)).symm)

theorem identitySource {m : Ram} {dst : BitVec 64}
    (loaded : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (w : Writable Extracted.programImage m dst 120) :
    Readable m 0x202d48 120 ∧ (0x202dc0 ≤ dst.toNat ∨ dst.toNat + 120 ≤ 0x202d48) := by
  apply Generate.Generator.Affine.readableCodeSpan (code := Extracted.programImage) _
    loaded (by decide) (by decide) w (by decide)
  intro i hi
  exact ⟨_, identityCode (Or.inl rfl) _ (mem_codeRange 0x202d48 identityBytes i
    (by simpa only [identityBytes, List.length_ofFn] using hi))⟩

end K256.Proofs.Verify.Core.Lincomb.Loop
