import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open SecretKeyFromBytes.Scalar

theorem movsq [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {d : Nat}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100d8e)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (source : t.regValue .rsi = stackPtr t + 80)
    (count : t.regValue .rcx = 13)
    (scalar : Nat256At t (stackPtr t + 80) d)
    (point : Sec1.AffineAt t (stackPtr t + 112) (Points.mul d Operations.domain.G)) :
    ∃ u, Advances boundary 13 t u ∧ State s u ∧ u.RIP = 0x100d91 ∧
      Nat256At u (s.regValue .rdi) d ∧
      Sec1.AffineAt u (s.regValue .rdi + 32) (Points.mul d Operations.domain.G) ∧
      u.regValue .rax = t.regValue .rax := by
  have hn : (rcx.read t).toNat = 13 := by change (t.regValue .rcx).toNat = 13; rw [count]; rfl
  have readable : MemReadable t (t.regValue .rsi) 104 := by
    rw [source]
    exact state.stack_readable pre (by decide)
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 104 := by
    rw [destination]
    have h := readable_of_grow (memoryRegion_memReadable pre.outputBounded pre.outputAllocated
      (Nat.le_refl _) (Nat.le_refl _)) state.allocated
    refine ⟨h, tables_of_not_reserved (by decide) h.low ?_⟩
    intro i hi hp
    exact pre.avoids _ (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hp)
  have apart : (t.regValue .rsi).toNat + 104 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 104 ≤ (t.regValue .rsi).toNat := by
    have addr : stackPtr t + 80 = stackPtr s - 184 :=
      scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)
    have sr : (t.regValue .rsi).toNat = (stackPtr s).toNat - 184 := by
      rw [source,addr]
      exact stack_sub_toNat pre.stack (by decide)
    have bounds := stack_bounds pre.stack
    have hd := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
    by_cases h : (t.regValue .rsi).toNat + 104 ≤ (t.regValue .rdi).toNat
    · exact .inl h
    right
    apply Nat.le_of_not_lt
    intro he
    apply hd (max (t.regValue .rsi).toNat (t.regValue .rdi).toNat)
    · change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + 104
      rw [destination] at h he ⊢
      omega
    · change (stackPtr s).toNat - 3624 ≤ _ ∧
        _ < (Stack.region s 3624).start + (Stack.region s 3624).size
      rw [stack_region_end,sr]
      rw [sr] at h he
      omega
  have dst : rdi.read t = s.regValue .rdi := destination
  have src : rsi.read t = stackPtr t + 80 := source
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip
    state.directionFlag.df hn readable writable apart (by
      intro i hi j hj he
      rw [dst] at he
      apply pre.avoids _ (by simp) _
        (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      left
      rw [he]
      change InProgram ((Extracted.textAddress + BitVec.ofNat 64 0xd8e) + BitVec.ofNat 64 j)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset (0xd8e+j) (by omega))
  obtain ⟨run,ready,effect,copied⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution state.bindingsSupported.stringStride
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xd8e [0xf3,0x48,0xa5]
        (by decide) (by decide +kernel)) pc hn
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd8e (by decide)))
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd91 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize hu : nextStates 13 t = u at run ready effect copied
  have g : AgreesExcept [.reg 6,.reg 7,.reg 1,.mem (s.regValue .rdi) 104,.rip] t u := by
    simpa only [repMovsqEffect_components,hn,Nat.reduceMul,dst] using effect.agrees
  have next := state.after pre ready g (by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    obtain ⟨i,hi,rfl⟩ := ha
    exact ⟨registerRegion s .rdi 104,by simp [bodyWrites],
      memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi⟩)
    (g.read (n := 64) (r := 4) (by simp))
  refine ⟨u,run,next,effect.rip,?_,?_,g.read (n := 64) (r := 0) (by simp)⟩
  · refine ⟨scalar.1,fun i hi => ?_⟩
    have h := copied i (by omega : i < 104)
    rw [dst,src] at h
    exact h.trans (scalar.2 i hi)
  · apply point.of_bytes_eq
    intro i hi
    have h := copied (32+i) (by omega)
    rw [dst,src] at h
    rw [BitVec.ofNat_add] at h
    change u.external[s.regValue .rdi + (32 + BitVec.ofNat 64 i)]? =
      t.external[(stackPtr t + 80) + (32 + BitVec.ofNat 64 i)]? at h
    rw [← BitVec.add_assoc (stackPtr t + 80) 32 _,
      BitVec.add_assoc (stackPtr t) 80 32,
      ← BitVec.add_assoc (s.regValue .rdi) 32 _] at h
    exact h

end P256.Proofs.Generate.Sampler.Finish
