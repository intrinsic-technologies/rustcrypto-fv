import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def transferComponents (s : RamState) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (s.regValue .rdi) 96, .rip]

theorem transfer [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (rip : t.RIP = 0x103437) (src : t.regValue .rsi = stackPtr s - 336)
    (dst : t.regValue .rdi = s.regValue .rdi) (count : t.regValue .rcx = 12)
    (input : ProjectiveAt t (stackPtr s - 336) point) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u 96 1400 376 ∧ u.RIP = 0x10343a ∧
      ProjectiveAt u (s.regValue .rdi) point ∧ AgreesExcept (transferComponents s) t u := by
  have hn : (rcx.read t).toNat = 12 := by rw [show rcx.read t = 12#64 from count]; rfl
  have source : MemReadable t (rsi.read t) 96 := by
    change MemReadable t (t.regValue .rsi) 96
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack
      (offset := 336) (len := 96) (by decide) (by decide)) state.allocated
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (rdi.read t) 96 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 96
    rw [dst]
    exact output_writable pre.toCalleePre (by decide) state.allocated
  have bounds := stack_bounds pre.stack
  have sn : (stackPtr s - 336).toNat = (stackPtr s).toNat - 336 :=
    stack_sub_toNat pre.stack (by decide)
  have disjoint : (rsi.read t).toNat + 96 ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 96 ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat
    rw [src, dst, sn]
    by_cases h : (stackPtr s).toNat - 336 + 96 ≤ (s.regValue .rdi).toNat
    · exact Or.inl h
    right
    apply Nat.le_of_not_lt
    intro h'
    let address := max ((stackPtr s).toNat - 336) (s.regValue .rdi).toNat
    have sep := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) address
    apply sep
    · change (s.regValue .rdi).toNat ≤ address ∧ address < (s.regValue .rdi).toNat + 96
      dsimp only [address]
      constructor <;> omega
    · change (stackPtr s).toNat - 1400 ≤ address ∧
        address < (Stack.region s 1400).start + (Stack.region s 1400).size
      rw [stack_region_end]
      dsimp only [address]
      constructor <;> omega
  have apart : RangeApart (rdi.read t) 96 0x103437 3 := by
    change RangeApart (t.regValue .rdi) 96 0x103437#64 3
    rw [dst]
    simpa only [Extracted.textAddress, BitVec.reduceAdd] using
      (output_code pre.toCalleePre (offset := 0x3437) (len := 3) (by decide))
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory
    rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, bytes⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
    pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3437 [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3437 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x343a (by decide)))
  simp only [show max 12 1 = 12 from rfl] at run ready effect bytes
  generalize hu : nextStates 12 t = u at run ready effect bytes
  have frame : AgreesExcept (transferComponents s) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = s.regValue .rdi from dst,
      Nat.reduceMul, transferComponents] using effect.agrees
  have writes : WritesWithin (transferComponents s) #v[registerRegion s .rdi 96, workRegion s 1400] := by
    intro c hc a ha
    simp only [transferComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨registerRegion s .rdi 96, by simp,
      memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show i < 96 by omega)⟩
  refine ⟨u, run, state.after_effect pre.toCalleePre (by decide) ready frame writes
    (by simp [transferComponents]), effect.rip, ?_, frame⟩
  apply input.of_bytes_eq
  intro i hi
  have hb := bytes i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb

end P256.Proofs.Projective.Multiply.Machine.Loop
