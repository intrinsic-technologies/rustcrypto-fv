import P256.Proofs.Sec1.SquareRoot.Prepare.Memory
import P256.Proofs.Sec1.SquareRoot.Parameters
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Common.Instructions.RepMovsqAny

namespace P256.Proofs.Sec1.SquareRoot.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem parameter_byte_inProgram {i : Nat} (hi : i < 112) :
    InProgram (0x202f28 + BitVec.ofNat 64 i) := by
  have hb : ∀ j : Fin 112,
      Extracted.programSections.fetchByte (0x202f28 + BitVec.ofNat 64 j.val) =
        some parameterBytes[j.val]! := by decide +kernel
  exact ⟨_, hb ⟨i, hi⟩⟩

theorem parameter_stack_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    0x202f28 + 112 ≤ (stackPtr s - 360#64).toNat ∨
      (stackPtr s - 360#64).toNat + 112 ≤ 0x202f28 := by
  have hs := stack_bounds pre.stack
  have hd := stack_sub_toNat pre.stack (offset := 360) (by decide)
  by_cases hbefore : 0x202f28 + 112 ≤ (stackPtr s - 360#64).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  let a := max 0x202f28 (stackPtr s - 360#64).toNat
  have ha : a < 2^64 := by dsimp only [a]; omega
  have he : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
  have him : InProgram (BitVec.ofNat 64 a) := by
    have hi : a - 0x202f28 < 112 := by dsimp only [a]; omega
    have h := parameter_byte_inProgram hi
    have hadd : 0x202f28 + BitVec.ofNat 64 (a - 0x202f28) = BitVec.ofNat 64 a := by
      rw [show (0x202f28 : BitVec 64) = BitVec.ofNat 64 0x202f28 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [hadd] at h
  apply pre.avoids (Stack.region s 2176) (by simp) (BitVec.ofNat 64 a) _ (.inl him)
  change (stackPtr s).toNat - 2176 ≤ (BitVec.ofNat 64 a).toNat ∧
    (BitVec.ofNat 64 a).toNat < (stackPtr s).toNat - 2176 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 2176))
  rw [he]
  dsimp only [a]
  omega

theorem parameter_copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (loaded : ProgramLoaded t) (direction : DirectionFlagClear t.RFLAGS)
    (rip : t.RIP = 0x114468) (src : t.regValue .rsi = 0x202f28)
    (dst : t.regValue .rdi = stackPtr s - 360#64) (count : t.regValue .rcx = 14)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    P256.Proofs.Common.Instructions.RepMovsqAny.RepMovsqPre 0x114468 t := by
  have hn : (rcx.read t).toNat = 14 := by change (t.regValue .rcx).toNat = 14; rw [count]; rfl
  have hd := readable_of_grow
    (stack_sub_readable pre.stack (offset := 360) (len := 112) (by decide) (by decide)) grow
  have hp := parameters_loaded loaded
  have hb := stack_bounds pre.stack
  have hnat := stack_sub_toNat pre.stack (offset := 360) (by decide)
  refine ⟨rip, direction, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn]; change (t.regValue .rsi).toNat + 112 ≤ 2^32; rw [src]; decide
  · rw [hn]; change (t.regValue .rdi).toNat + 112 ≤ 2^32; rw [dst]; exact hd.low
  · rw [hn]; change ∀ i < 112, (t.external[t.regValue .rsi + BitVec.ofNat 64 i]?).isSome
    rw [src]
    intro i hi
    rw [hp i hi]
    rfl
  · rw [hn]; change ∀ i < 112, (t.external[t.regValue .rdi + BitVec.ofNat 64 i]?).isSome
    rw [dst]; exact hd.mem
  · rw [hn]; change (t.regValue .rsi).toNat + 112 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 112 ≤ (t.regValue .rsi).toNat
    rw [src, dst]
    exact parameter_stack_disjoint pre
  · rw [hn]; change PageTableEntriesApart (t.regValue .rdi).toNat 112
    rw [dst]
    apply tables_of_not_reserved (by decide) hd.low
    intro i hi hin
    exact pre.avoids (Stack.region s 2176) (by simp) _
      (ScalarFrame.stack_contains pre (by decide) (by decide) ⟨i, hi, rfl⟩) (.inr hin)
  · rw [hn]; change RangeApart (t.regValue .rdi) 112 0x114468 3
    rw [dst]
    exact stack_code pre (pc := 0x14468) (by decide) (by decide) (by decide)

theorem parameter_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t) (direction : DirectionFlagClear t.RFLAGS)
    (rip : t.RIP = 0x114468) (src : t.regValue .rsi = 0x202f28)
    (dst : t.regValue .rdi = stackPtr s - 360#64) (count : t.regValue .rcx = 14)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    ∃ u, Advances boundary 14 t u ∧ ReadyToStep u ∧ u.RIP = 0x11446b ∧
      ParametersAt u (stackPtr s - 360#64) ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - 360#64) 112, .rip] t u := by
  have pc := parameter_copy_pre pre loaded direction rip src dst count grow
  have hn : (rcx.read t).toNat = 14 := by change (t.regValue .rcx).toNat = 14; rw [count]; rfl
  have code := programText_slice (programLoaded_codeIn loaded) 0x14468 [0xf3,0x48,0xa5]
    (by decide) (by decide +kernel)
  obtain ⟨run, hr, effect, copy⟩ := rep_movsq_execution pre.bindingsSupported.stringStride ready code pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x14468 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1446b (by decide)))
  refine ⟨nextStates 14 t, run, hr, effect.rip, ?_, ?_⟩
  · intro i hi
    have hb := copy i hi
    change (nextStates 14 t).external[t.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
    rw [src, dst] at hb
    exact hb.trans (parameters_loaded loaded i hi)
  · have hag := effect.agrees
    rw [repMovsqEffect_components, hn] at hag
    change AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) 112, .rip] t _ at hag
    rwa [dst] at hag

end P256.Proofs.Sec1.SquareRoot.Prepare
