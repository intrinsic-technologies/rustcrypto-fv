import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Epilogue
import P256.Proofs.Projective.Multiply.Machine.Lookup.Copy
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 96 := by
  have readable := readable_of_grow
    (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
    state.allocated
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved (by change 0 < 96; decide) readable.low
  intro i hi hreserved
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hreserved)

theorem output_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) {offset len : Nat}
    (bound : offset + len ≤ 118431) : RangeApart (s.regValue .rdi) 96
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + j) (by omega)

def transferComponents (s : RamState) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (s.regValue .rdi) 96, .rip]

theorem transfer [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (rip : t.RIP = 0x10495b) (src : t.regValue .rsi = stackPtr s - 344)
    (dst : t.regValue .rdi = s.regValue .rdi) (count : t.regValue .rcx = 12)
    (input : ProjectiveAt t (stackPtr s - 344) point) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u ∧ u.RIP = 0x10495e ∧
      ProjectiveAt u (s.regValue .rdi) point ∧ AgreesExcept (transferComponents s) t u := by
  have hn : (rcx.read t).toNat = 12 := by rw [show rcx.read t = 12#64 from count]; rfl
  have source : MemReadable t (rsi.read t) 96 := by
    change MemReadable t (t.regValue .rsi) 96
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack
      (offset := 344) (len := 96) (by decide) (by decide)) state.allocated
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (rdi.read t) 96 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 96
    rw [dst]
    simpa only [BitVec.add_zero] using (output_writable pre state).add 0 (len := 96) (by decide)
  have bounds := stack_bounds pre.stack
  have sn : (stackPtr s - 344).toNat = (stackPtr s).toNat - 344 :=
    stack_sub_toNat pre.stack (by decide)
  have disjoint : (rsi.read t).toNat + 96 ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 96 ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat
    rw [src, dst, sn]
    by_cases h : (stackPtr s).toNat - 344 + 96 ≤ (s.regValue .rdi).toNat
    · exact Or.inl h
    right
    apply Nat.le_of_not_lt
    intro h'
    let address := max ((stackPtr s).toNat - 344) (s.regValue .rdi).toNat
    have sep := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) address
    apply sep
    · change (s.regValue .rdi).toNat ≤ address ∧ address < (s.regValue .rdi).toNat + 96
      dsimp only [address]
      constructor <;> omega
    · change (stackPtr s).toNat - 496 ≤ address ∧
        address < (Stack.region s 496).start + (Stack.region s 496).size
      rw [stack_region_end]
      dsimp only [address]
      constructor <;> omega
  have apart : RangeApart (rdi.read t) 96 0x10495b 3 := by
    change RangeApart (t.regValue .rdi) 96 0x10495b#64 3
    rw [dst]
    have ha := P256.Proofs.Common.Instructions.RangeApart.add_left (h := (output_code pre (offset := 0x495b) (len := 3) (by decide)))
      0 (len := 96) (by decide)
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using ha
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x495b [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x495b (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x495e (by decide)))
  simp only [show max 12 1 = 12 from rfl] at run ready effect bytes
  generalize hu : nextStates 12 t = u at run ready effect bytes
  have frame : AgreesExcept (transferComponents s) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = s.regValue .rdi from dst,
      Nat.reduceMul, transferComponents] using effect.agrees
  have writes : WritesWithin (transferComponents s) #v[registerRegion s .rdi 96, workRegion s] := by
    intro c hc a ha
    simp only [transferComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨registerRegion s .rdi 96, by simp,
      memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show i < 96 by omega)⟩
  refine ⟨u, run, after pre state ready frame writes (by simp [transferComponents]), effect.rip, ?_, frame⟩
  apply input.of_bytes_eq
  intro i hi
  have hb := bytes i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
