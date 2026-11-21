import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Sec1.Affine.Identity.Data
import P256.Proofs.Sec1.Affine.Representation
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Identity

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem identity_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : AffineDecodePre s boundary ⟨#[0]⟩) :
    0x202df8 + 72 ≤ (s.regValue .rdi).toNat ∨ (s.regValue .rdi).toNat + 72 ≤ 0x202df8 := by
  apply Classical.byContradiction
  intro h
  have overlap : (s.regValue .rdi).toNat < 0x202df8 + 72 ∧
      0x202df8 < (s.regValue .rdi).toNat + 72 := by omega
  by_cases before : (s.regValue .rdi).toNat ≤ 0x202df8
  · apply pre.avoids (registerRegion s .rdi 80) (by simp) 0x202df8
    · change (s.regValue .rdi).toNat ≤ 0x202df8 ∧ 0x202df8 < (s.regValue .rdi).toNat + 80
      omega
    · exact .inl (by simpa only [BitVec.add_zero] using identity_byte_inProgram (i := 0) (by decide))
  · have hi : (s.regValue .rdi).toNat - 0x202df8 < 72 := by omega
    have address : (0x202df8 : BitVec 64) + BitVec.ofNat 64 ((s.regValue .rdi).toNat - 0x202df8) =
        s.regValue .rdi := by
      rw [← BitVec.ofNat_sub_ofNat_of_le (s.regValue .rdi).toNat 0x202df8 (by decide : 0x202df8 < 2^64) (by omega)]
      simp only [BitVec.ofNat_toNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    apply pre.avoids (registerRegion s .rdi 80) (by simp) (s.regValue .rdi)
    · change (s.regValue .rdi).toNat ≤ (s.regValue .rdi).toNat ∧
        (s.regValue .rdi).toNat < (s.regValue .rdi).toNat + 80
      omega
    · exact .inl (address ▸ identity_byte_inProgram hi)

theorem copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : AffineDecodePre s boundary ⟨#[0]⟩) (state : Frame s t)
    (rip : t.RIP = 0x110629) (src : t.regValue .rsi = 0x202df8)
    (dst : t.regValue .rdi = s.regValue .rdi) (count : t.regValue .rcx = 9) :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP = 0x11062c ∧
      AffineAt u (s.regValue .rdi) .infinity ∧ u.regValue .rbx = t.regValue .rbx := by
  have hn : (rcx.read t).toNat = 9 := by change (t.regValue .rcx).toNat = 9; rw [count]; rfl
  have source : MemReadable t (rsi.read t) 72 := by
    change MemReadable t (t.regValue .rsi) 72
    rw [src]
    exact identity_readable state.loaded
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (rdi.read t) 72 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 72
    rw [dst]
    simpa only [BitVec.add_zero] using
      (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add 0 (len := 72) (by decide)
  have disjoint : (rsi.read t).toNat + 72 ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 72 ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 72 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 72 ≤ (t.regValue .rsi).toNat
    rw [src, dst]
    exact identity_disjoint pre
  have apart : RangeApart (rdi.read t) 72 0x110629 3 := by
    change RangeApart (t.regValue .rdi) 72 0x110629#64 3
    rw [dst]
    have ha := P256.Proofs.Common.Instructions.RangeApart.add_left
      (ScalarFrame.output_code pre.toCalleePre (offset := 0x10629) (len := 3) (by decide))
      0 (len := 72) (by decide)
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using ha
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10629 [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10629 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1062c (by decide)))
  simp only [show max 9 1 = 9 from rfl] at run ready effect bytes
  generalize hu : nextStates 9 t = u at run ready effect bytes
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (s.regValue .rdi) 72, .rip] t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = s.regValue .rdi from dst,
      Nat.reduceMul] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7, .reg 1, .mem (s.regValue .rdi) 72, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨registerRegion s .rdi 80, by simp,
      memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show i < 80 by omega)⟩
  refine ⟨u, run, state.after_effect pre.toCalleePre (by decide) ready agrees writes (by simp),
    effect.rip, ?_, agrees.read (n := 64) (r := 3) (by simp)⟩
  apply (identity_at state.loaded).of_bytes_eq
  intro i hi
  have hb := bytes i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb

end P256.Proofs.Sec1.Affine.Identity
