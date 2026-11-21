import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Stage
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.CopyArguments

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem stack_sources_disjoint [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {src dst : Nat} (pre : Pre s boundary) (hs : src ≤ 1400) (hd : dst ≤ 1400)
    (source : t.regValue .rsi = stackPtr s-BitVec.ofNat 64 src)
    (destination : t.regValue .rdi = stackPtr s-BitVec.ofNat 64 dst)
    (apart : src+96 ≤ dst ∨ dst+96 ≤ src) :
    (t.regValue .rsi).toNat+96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat+96 ≤ (t.regValue .rsi).toNat := by
  rw [source, destination, stack_sub_toNat pre.stack hs, stack_sub_toNat pre.stack hd]
  have := stack_bounds pre.stack
  omega

theorem prepare_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n : Nat} {point : Projective} (pre : Pre s boundary)
    (state : RoundState s t n 0x103380 336 point)
    (rax : t.regValue .rax = stackPtr s-144) :
    ∃ fuel u, Advances boundary fuel t u ∧ RoundState s u n 0x10338e 144 point := by
  obtain ⟨fuel, v, run, ready, _, effect⟩ := copyArguments_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3380 copyArgumentsBytes
      (by decide) (by decide +kernel)) state.rip
  have agrees : AgreesExcept [.reg 1, .reg 7, .reg 6, .rip] t v := effect.agrees
  have sv := state.after_registers ready agrees effect.rip
    (by simp [Component.Covers]) (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hw : v.regValue .rcx = 12 ∧ v.regValue .rdi = t.regValue .rax ∧
      v.regValue .rsi = t.regValue .r13 := effect.writes
  have dst : v.regValue .rdi = stackPtr s-144 := hw.2.1.trans rax
  have src : v.regValue .rsi = stackPtr s-336 := hw.2.2.trans state.r13
  have input : ProjectiveAt v (v.regValue .rsi) point := by rw [src]; exact sv.value
  have readable : MemReadable v (v.regValue .rsi) 96 := by
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 336)
      (by decide) (by decide)) sv.allocated
  obtain ⟨u, copied, su, ripU, value, frame⟩ := Copy.copy_to_stack pre.toCalleePre sv.toFrameState
    0x338b (by decide) (by decide +kernel) sv.rip 144 (by decide) (by decide)
    dst hw.1 readable (stack_sources_disjoint pre (by decide) (by decide) src dst (by decide)) input
  exact ⟨fuel+12, u, run.trans copied,
    sv.after_copy pre su ripU value frame (by decide) (by decide)⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
