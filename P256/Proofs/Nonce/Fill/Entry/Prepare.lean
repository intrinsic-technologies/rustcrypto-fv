import P256.Proofs.Nonce.Fill.Entry.Allocate
import P256.Proofs.Nonce.Fill.Entry.Prefix
import P256.Proofs.Nonce.Fill.Entry.Guard
import P256.Proofs.Nonce.Fill.Entry.Memory
import P256.Proofs.Nonce.Fill.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Prepared [Bindings] (initial s : RamState) (order : BitVec 64) (state : State) : Prop extends
    Frame initial s where
  rip : s.RIP = 0x10735a
  rdi : s.regValue .rdi = initial.regValue .rdi
  rcx : s.regValue .rcx = initial.regValue .rdi + 8
  r13 : s.regValue .r13 = 32
  outputSlot : memLoad s.external (frameBase initial + 40) 64 = initial.regValue .rsi
  generator : GeneratorAt s (initial.regValue .rdi) order state

theorem prepare [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {order : BitVec 64} {state : State} (pre : Pre initial boundary order state) :
    ∃ fuel t, Advances boundary fuel initial t ∧ Prepared initial t order state := by
  obtain ⟨s, runS, frameS, ripS, agreesS⟩ := allocate pre
  have pp : PrefixPre s := by
    refine ⟨ripS, ?_, ?_⟩
    · intro off ho
      have h : off = 40 := by simpa using ho
      subst off
      exact stack_writable8 pre frameS (by decide) (by decide)
    · intro off ho co cl hc
      have h : off = 40 := by simpa using ho
      subst off
      exact stack_code pre frameS (by decide) hc
  obtain ⟨fuel, u, runU, readyU, _, effect⟩ := prefix_block boundary pre.outerBoundary s
    (readyToStep frameS.machine frameS.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameS.loaded) 0x7341 prefixBytes
      (by decide) (by decide +kernel)) pp
  have writes : WritesWithin (prefixEffect s).components (workRegions initial) := by
    intro c hc a ha
    simp only [Effect.components, prefixEffect, BitVec.ofNat_eq_ofNat,
      List.map_cons, Write.component_reg, Write.component_mem, Nat.reduceDiv, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨_, by simp [workRegions], stack_component pre frameS (off := 40) (by decide) ha⟩
  have frameU := frameS.after_effect pre readyU effect.agrees writes (by component_not_mem)
  have memoryU : MemoryWriteFrame s u #v[Stack.region initial 2096] := by
    apply stack_frame pre frameS effect.agrees
    intro c hc a ha
    simp only [Effect.components, prefixEffect, BitVec.ofNat_eq_ofNat,
      List.map_cons, Write.component_reg, Write.component_mem, Nat.reduceDiv, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨40, 8, by decide, ha⟩
  have rdxS : s.regValue .rdx = 32 :=
    (agreesS.read (n := 64) (r := 2) (by simp [saveFrame])).trans pre.outputLength
  have rdiS : s.regValue .rdi = initial.regValue .rdi :=
    agreesS.read (n := 64) (r := 7) (by simp [saveFrame])
  have rsiS : s.regValue .rsi = initial.regValue .rsi :=
    agreesS.read (n := 64) (r := 6) (by simp [saveFrame])
  have rdxU : u.regValue .rdx = 32 :=
    (effect.agrees.read (n := 64) (r := 2) (by component_not_mem)).trans rdxS
  obtain ⟨t, runT, readyT, ripT, agreesT⟩ := guard
    (readyToStep frameU.machine frameU.bindingsSupported) frameU.loaded effect.rip rdxU pre.outerBoundary
  have memoryT := agreesT.external (by simp [Component.Covers])
  have frameT := frameU.after_registers readyT agreesT (by simp [Component.Covers]) (by simp)
  have totalMemory := memoryWriteFrame_trans
    (ScalarFrame.save_frame pre.toCalleePre (by decide) agreesS (by simp [Component.Covers])) memoryU
  have generatorU := pre.generator.of_frame pre.outputBounded pre.orderBounded totalMemory
    (by intro r hr; have h : r = Stack.region initial 2096 := by simpa using hr
        subst r; exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide))
    (by intro r hr; have h : r = Stack.region initial 2096 := by simpa using hr
        subst r; exact pre.orderDisjoint _ (by simp))
  have rcxU : u.regValue .rcx = s.regValue .rdi + 8 := effect.writes.2.2
  rw [rdiS] at rcxU
  refine ⟨7 + fuel + 2, t, (runS.trans runU).trans runT,
    frameT, ripT, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((effect.agrees.trans agreesT).read (n := 64) (r := 7) (by component_not_mem)).trans rdiS
  · exact (agreesT.read (n := 64) (r := 1) (by simp)).trans
      rcxU
  · exact (agreesT.read (n := 64) (r := 13) (by simp)).trans (effect.writes.1.trans rdxS)
  · rw [memoryT, ← frameS.rsp]
    exact effect.writes.2.1.trans rsiS
  · simpa only [GeneratorAt, DrbgAt, SecretKeyFromBytes.Scalar.Nat256At, memoryT] using generatorU

end P256.Proofs.Nonce.Fill.Entry
