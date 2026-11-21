import K256.Proofs.Generate.Generator.Multiply.Caller.TableCopies
import K256.Proofs.Generate.Generator.Affine.Select.Setup
import K256.Proofs.Common.Image

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def identityCopies (m : Ram) (sp : BitVec 64) : Nat → Ram
  | 0 => m
  | i + 1 => memCopy (identityCopies m sp i) (sp + BitVec.ofNat 64 (1928 + 120*i)) 0x202c40 120

def secondCopyMemory (m : Ram) (sp : BitVec 64) : Ram :=
  memCopy (memStore (identityCopies m sp 16) (sp - 8) (0x10f091 : BitVec 64))
    (sp + 8) (sp + 1928) 960

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
    ∃ b, ((0x202c40 : BitVec 64) + BitVec.ofNat 64 i, b) ∈ Extracted.programImage := by
  apply exists_mem_toCodeMap (s := rodataSection) (by simp [rodataSection, Extracted.programSections])
  · change 0x200000 ≤ ((0x202c40 : BitVec 64) + BitVec.ofNat 64 i).toNat
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  · change ((0x202c40 : BitVec 64) + BitVec.ofNat 64 i).toNat < 0x200000 + Extracted.rodataBytes.size
    simp only [Common.rodataBytes_size, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega

private theorem identityCopyGuard {m copied : Ram} {sp pc off : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 3856)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (eq : copied = identityCopies m sp ((off.toNat - 1928) / 120))
    (fits : (off - (0 - 8)).toNat + 120 ≤ 3856)
    (within : (pc - 0x10ef08).toNat + 3 ≤ bytes_l10ef08.length) :
    RepMovsOk Extracted.programImage copied 0 0x202c40 (sp + off) 15 8 pc 3 := by
  subst copied
  have dst : Writable Extracted.programImage m (sp + off) 120 :=
    window.of_offsets rfl (addr_sub sp 8) fits
  obtain ⟨src, apart⟩ := Affine.readableCodeSpan identitySpan image (by decide) (by decide) dst (by decide)
  have h := ParseSignature.storeOk_of_codeRange (off := (pc - 0x10ef08).toNat)
    (identityCopies_writable (sp := sp) dst ((off.toNat - 1928) / 120))
    (fun x hx => Common.fnCode_subset_programImage x (code_l10ef08 x hx)) within
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, show 0x10ef08 + (pc - 0x10ef08) = pc by bv_omega] at h
  exact ⟨rfl, src.low, h.low, (identityCopies_readable (sp := sp) src ((off.toNat - 1928) / 120)).present, h.present,
    apart, h.tables, h.apart, h.notCode⟩

set_option maxRecDepth 4096 in
private theorem identityCopyCall {a : Registers} {m : Ram} {sp : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 3856)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820) (df : a[22].get 1 = 0) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10ef08, a, m⟩ =
        .call ⟨.l12a820, b, memStore (identityCopies m sp 16) (sp - 8) (0x10f091 : BitVec 64)⟩
          (callFrame .l10f091 0x10f091) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 8 ∧ b[6].get 64 = sp + 1928 ∧
      b[2].get 64 = 960 ∧ b[12] = ⟨64, sp + 8⟩ ∧ b[15] = ⟨64, sp + 2888⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → i.val ≠ 12 → i.val ≠ 15 → b[i] = a[i] := by
  have slot : Writable Extracted.programImage (identityCopies m sp 16) (sp - 8) 8 :=
    identityCopies_writable (window.sub (Nat.le_refl _) (by omega)) 16
  have push : StoreOk Extracted.programImage (identityCopies m sp 16) (sp - 8) 8 0x10f08e 3 :=
    by slot_guard using code_l10ef08
  refine ⟨?_, ?run, ?post⟩
  case run =>
    generate_block [rsp, target, df]
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

theorem secondCopy {a : Registers} {m : Ram} {sp : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 3856)
    (image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2)
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820) (df : a[22].get 1 = 0) :
    ∃ b, Reaches .l10ef08 a m .l10f091 b (secondCopyMemory m sp) ∧
      b[4] = ⟨64, sp⟩ ∧ b[12] = ⟨64, sp + 8⟩ ∧ b[15] = ⟨64, sp + 2888⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → i.val ≠ 12 → i.val ≠ 15 → b[i] = a[i] := by
  obtain ⟨b, call, hsp, dst, src, n, left, right, keep⟩ := identityCopyCall window image rsp target df
  have w := identityCopies_writable (sp := sp) window 16
  have flag := (congrArg (Value.get 1) (keep 22 (by decide) (by decide) (by decide))).trans df
  obtain ⟨c, run, top, saved⟩ := stackCopy w (by decide) (by decide) (by decide) (by decide)
    (by decide) call hsp dst src n flag
  exact ⟨c, run, top, (saved 12 (by decide)).trans left, (saved 15 (by decide)).trans right,
    fun i hi h12 h15 => (saved i hi).trans (keep i hi h12 h15)⟩

end K256.Proofs.Generate.Generator.Multiply.Caller
