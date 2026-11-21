import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Sec1.Affine.Identity.Data
import P256.Proofs.Sec1.Affine.Representation
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

theorem constant_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) :
    0x202df8 + 72 ≤ (stackPtr s - 592).toNat ∨
      (stackPtr s - 592).toNat + 72 ≤ 0x202df8 := by
  have hs := stack_bounds pre.stack
  have hn : (stackPtr s - 592).toNat = (stackPtr s).toNat - 592 :=
    stack_sub_toNat pre.stack (by decide)
  by_cases hbefore : 0x202df8 + 72 ≤ (stackPtr s - 592).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  let a := max 0x202df8 (stackPtr s - 592).toNat
  have ha : a < 2^64 := by dsimp only [a]; have := (stackPtr s - 592).isLt; omega
  have he : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
  have him : InProgram (BitVec.ofNat 64 a) := by
    have h := identity_byte_inProgram (i := a - 0x202df8) (by dsimp only [a]; omega)
    have hadd : 0x202df8 + BitVec.ofNat 64 (a - 0x202df8) = BitVec.ofNat 64 a := by
      rw [show (0x202df8 : BitVec 64) = BitVec.ofNat 64 0x202df8 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [hadd] at h
  apply pre.avoids (Stack.region s 3360) (by simp) (BitVec.ofNat 64 a) _ (.inl him)
  change (Stack.region s 3360).start ≤ _ ∧ _ <
    (Stack.region s 3360).start + (Stack.region s 3360).size
  rw [he, stack_region_end]
  change 3360 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at hs
  change (stackPtr s).toNat - 3360 ≤ a ∧ a < (stackPtr s).toNat + 8
  dsimp only [a]
  omega

def constantComponents (s : RamState) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - 592) 72, .rip]

theorem copy_constants [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110c92) (src : t.regValue .rsi = 0x202df8)
    (dst : t.regValue .rdi = stackPtr s - 592) (count : t.regValue .rcx = 9) :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP = 0x110c95 ∧
      AffineAt u (stackPtr s - 592) .infinity ∧ AgreesExcept (constantComponents s) t u := by
  have hn : (rcx.read t).toNat = 9 := by change (t.regValue .rcx).toNat = 9; rw [count]; rfl
  have source : MemReadable t (rsi.read t) 72 := by
    change MemReadable t (t.regValue .rsi) 72
    rw [src]
    exact identity_readable state.loaded
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (rdi.read t) 72 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 72
    rw [dst]
    have h := ScalarFrame.stack_writable pre.toCalleePre state (offset := 168) (len := 72)
      (by decide) (by decide) (by decide)
    rwa [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)] at h
  have disjoint : (rsi.read t).toNat + 72 ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 72 ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 72 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 72 ≤ (t.regValue .rsi).toNat
    rw [src, dst]
    exact constant_disjoint pre
  have apart : RangeApart (rdi.read t) 72 0x110c92 3 := by
    change RangeApart (t.regValue .rdi) 72 0x110c92#64 3
    rw [dst]
    have h := ScalarFrame.stack_code pre.toCalleePre state (offset := 168) (len := 72)
      (codeOffset := 0x10c92) (codeLen := 3) (by decide) (by decide) (by decide)
    rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)] at h
    exact h
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10c92 [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10c92 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10c95 (by decide)))
  simp only [show max 9 1 = 9 from rfl] at run ready effect bytes
  generalize hu : nextStates 9 t = u at run ready effect bytes
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - 592) 72, .rip] t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = stackPtr s - 592 from dst,
      Nat.reduceMul] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - 592) 72, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨ScalarFrame.workRegion s 3360, by simp,
      ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  refine ⟨u, run, state.after_effect pre.toCalleePre (by decide) ready agrees writes (by simp),
    effect.rip, ?_, agrees⟩
  apply (identity_at state.loaded).of_bytes_eq
  intro i hi
  have hb := bytes i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb


end P256.Proofs.Sec1.Affine.Uncompressed.Output
