import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Caller.SecondCopy

namespace K256.Proofs.Ecdh.Wrapper.Tables

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Generate.Generator.Multiply.Caller

def identityCopies (m : Ram) (sp : BitVec 64) : Nat → Ram
  | 0 => m
  | i + 1 => memCopy (identityCopies m sp i) (sp + BitVec.ofNat 64 (2264 + 120*i)) 0x202420 120

theorem identityCopies_writable {m : Ram} {sp a : BitVec 64} {n : Nat}
    (w : Writable Extracted.programImage m a n) (i : Nat) :
    Writable Extracted.programImage (identityCopies m sp i) a n := by
  induction i with
  | zero => exact w
  | succ i ih => exact ih.memStore _ _

private theorem identityCopies_readable {m : Ram} {sp a : BitVec 64} {n : Nat}
    (r : Readable m a n) (i : Nat) : Readable (identityCopies m sp i) a n := by
  induction i with
  | zero => exact r
  | succ i ih => exact ih.memStore _ _

private theorem identitySpan (i : Nat) (hi : i < 120) :
    ∃ b, ((0x202420 : BitVec 64) + BitVec.ofNat 64 i, b) ∈ Extracted.programImage := by
  apply exists_mem_toCodeMap (s := rodataSection) (by simp [rodataSection, Extracted.programSections])
  · change 0x200000 ≤ ((0x202420 : BitVec 64) + BitVec.ofNat 64 i).toNat
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  · change ((0x202420 : BitVec 64) + BitVec.ofNat 64 i).toNat < 0x200000 + Extracted.rodataBytes.size
    simp only [Common.rodataBytes_size, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega

private theorem identityCopyGuard {m copied : Ram} {sp pc off : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 4192)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (eq : copied = identityCopies m sp ((off.toNat - 2264) / 120))
    (fits : (off - (0 - 8)).toNat + 120 ≤ 4192)
    (within : (pc - 0x1018b0).toNat + 3 ≤ bytes_l1018b0.length) :
    RepMovsOk Extracted.programImage copied 0 0x202420 (sp + off) 15 8 pc 3 := by
  subst copied
  have dst : Writable Extracted.programImage m (sp + off) 120 :=
    window.of_offsets rfl (addr_sub sp 8) fits
  obtain ⟨src, apart⟩ := Generate.Generator.Affine.readableCodeSpan identitySpan image (by decide) (by decide) dst (by decide)
  have h := ParseSignature.storeOk_of_codeRange (off := (pc - 0x1018b0).toNat)
    (identityCopies_writable (sp := sp) dst ((off.toNat - 2264) / 120))
    (fun x hx => Common.fnCode_subset_programImage x (code_l1018b0 x hx)) within
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, show 0x1018b0 + (pc - 0x1018b0) = pc by bv_omega] at h
  exact ⟨rfl, src.low, h.low, (identityCopies_readable (sp := sp) src ((off.toNat - 2264) / 120)).present, h.present,
    apart, h.tables, h.apart, h.notCode⟩

set_option maxRecDepth 4096 in
theorem identityCopyCall {a : Arguments} {m : Ram} {sp : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 4192)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820) (df : a[22].get 1 = 0)
    (push : StoreOk Extracted.programImage (identityCopies m sp 16) (sp - 8) 8 0x101a39 3) :
    ∃ b : Arguments, program.runBlock (dialect Extracted.programImage) ⟨.l1018b0, a, m⟩ =
        .call ⟨.l12a820, b, memStore (identityCopies m sp 16) (sp - 8) (0x101a3c : BitVec 64)⟩
          (callFrame .l101a3c 0x101a3c) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 344 ∧ b[6].get 64 = sp + 2264 ∧
      b[2].get 64 = 960 ∧ b[12] = ⟨64, sp + 344⟩ ∧ b[15] = ⟨64, sp + 3224⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → i.val ≠ 12 → i.val ≠ 15 → b[i] = a[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l1018b0, b_l1018b0_1, b_l1018b0_2, b_l1018b0_3, rsp, target, df]
    iterate 16
      refine Eq.trans (ite_eq_left ?_) ?_
      apply Or.inr
      apply identityCopyGuard window image
      · rfl
      · decide
      · decide +kernel
    refine Eq.trans (ite_eq_left push) ?_
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h h12 h15
    simp only [memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | contradiction

end K256.Proofs.Ecdh.Wrapper.Tables
