import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Encode.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.CrossPageStore

theorem store_header [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (rip : t.RIP = 0x10b346)
    (length : t.regValue .rax = BitVec.ofNat 64 (digits n).length)
    (values : ∀ i < 257, memLoad t.external (stackPtr t + 16 + BitVec.ofNat 64 i) 8 =
      BitVec.ofInt 8 (((digits n)[i]?).getD 0)) :
    ∃ u, Advances boundary 1 t u ∧ Memory s u cursor point ∧
      u.RIP = 0x10b34b ∧ u.regValue .rbx = t.regValue .rbx ∧
      NafAt u (stackPtr s - 352) n := by
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step_any 0x10b346 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xb346
        [0x48,0x89,0x44,0x24,0x08] (by decide) (by decide +kernel))
      ⟨rip, stack_writable pre state.toFrameState (offset := 8) (len := 8) (by decide) (by decide),
        stack_code pre state.toFrameState (offset := 8) (len := 8)
          (codeOffset := 0xb346) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb34b (by decide)))
  change ({rip := 0x10b34b, writes := [⟨(Operand.mem (stackPtr t + 8) : Operand 64), t.regValue .rax⟩]} : Effect).Holds t u at effect
  have agrees : AgreesExcept [.mem (stackPtr t + 8) 8, .rip] t u := by simpa [Effect.components] using effect.agrees
  have state' := state.after_store pre ready (offset := 8) (by decide) agrees
  have address : stackPtr t + 8 = stackPtr s - 352 := stack_address state.rsp (offset := 8) (by decide)
  refine ⟨u, run, state', effect.rip, agrees.read (n := 64) (r := 3) (by simp), ?_⟩
  rw [← address]
  constructor
  · exact effect.writes.trans length
  · intro i hi
    have address' : (stackPtr t + 8) + 8 = stackPtr t + 16 := by
      simp only [BitVec.add_assoc]; rfl
    rw [address', ← values i hi]
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
    intro j hj c hc cover
    have j0 : j = 0 := by omega
    subst j
    simp only [BitVec.add_zero] at cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨k, hk, he⟩ := cover
      exact RangeApart.offsets (stackPtr t) (a := 8) (b := 16) (len := 8) (count := 257)
        (by decide) (by decide) (.inl (by decide)) k hk i hi he.symm
    · exact cover.elim

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
