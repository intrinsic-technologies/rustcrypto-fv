import P256.Proofs.ReadBe.Loop.Head
import P256.Proofs.ReadBe.Loop.Arguments
import P256.Proofs.ReadBe.Frame

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def loopSetupComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .flags, .rip, .mem (frameBase s + 16) 8]

theorem frameBase_add16 (s : RamState) : frameBase s + 16 = stackPtr s - 56 := by
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem Pre.loop_setup_writes [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    WritesWithin (loopSetupComponents s) #v[registerRegion s .rdx 32, scratchRegion s] := by
  intro c hc a ha
  simp only [loopSetupComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨scratchRegion s, by simp, ?_⟩
  rw [frameBase_add16]
  exact pre.scratch_contains (offset := 56) (len := 8) (by decide) (by decide) (by decide) hi

structure LoopSetup [Bindings] (s t u : RamState) (boundary : ReturnBoundary)
    (k : Nat) : Prop where
  execution : ∃ fuel, Advances boundary fuel t u
  frame : Frame s u
  rip : u.RIP = 0x11912b
  count : u.regValue .rdx = 8
  source : u.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 (24-8*k)
  destination : u.regValue .rdi = frameBase s + 16
  agrees : AgreesExcept (loopSetupComponents s) t u

theorem loop_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {k : Nat} (pre : Pre s boundary) (state : LoopState s t input k)
    (hk : k < 4) : ∃ u, LoopSetup s t u boundary k := by
  have buffer : stackPtr t + 16 = stackPtr s - 56 := by
    rw [state.frame.rsp, frameBase_add16]
  have writable : MemWritable t (stackPtr t + 16) 8 := by
    rw [buffer]
    exact writable_of_grow (stack_sub_writable8 pre.stack pre.stack_avoids_tables (offset := 56)
      (by decide) (by decide)) state.frame.allocated
  have avoids : ∀ a, Component.Covers (.mem (stackPtr t + 16) 8) a → ¬ InProgram a := by
    intro a ha hp
    obtain ⟨i, hi, rfl⟩ := ha
    apply pre.avoids (Stack.region s 128) (by simp) _ ?_ (.inl hp)
    rw [buffer]
    exact pre.stack_contains (offset := 56) (len := 8) (by decide) (by decide) hi
  obtain ⟨v, run, ready, rip, ax, si, agree⟩ := loop_head
    (readyToStep state.frame.machine state.frame.bindingsSupported) state.frame.loaded
    (by simpa only [ite_eq_left hk] using state.rip)
    (by rw [state.remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    writable avoids pre.outerBoundary
  have agree' : AgreesExcept (loopSetupComponents s) t v := agree.mono (by
    rw [state.frame.rsp]
    simp [loopSetupComponents])
  have rsp : stackPtr v = frameBase s :=
    (agree.read (n := 64) (r := 4) (by simp)).trans state.frame.rsp
  have frame := state.frame.of_agrees pre ready agree' rsp pre.loop_setup_writes
  obtain ⟨fuel, u, advance, ready', _, effect⟩ := loop_arguments boundary pre.outerBoundary v
    ready (programText_slice (programLoaded_codeIn frame.loaded) 0x19110 loopArgumentsBytes
      (by decide +kernel) (by decide +kernel)) ⟨rip, ax, si⟩
  have agreeU : AgreesExcept [.reg 1, .reg 2, .reg 6, .reg 7, .flags, .rip] v u := effect.agrees
  have total : AgreesExcept (loopSetupComponents s) t u :=
    (agree'.trans agreeU).mono (by simp [loopSetupComponents])
  have rspU : stackPtr u = frameBase s :=
    (agreeU.read (n := 64) (r := 4) (by simp)).trans rsp
  refine ⟨u, ⟨⟨7 + fuel, run.trans advance⟩,
    state.frame.of_agrees pre ready' total rspU pre.loop_setup_writes,
    effect.rip, effect.writes.2.1, ?_, ?_, total⟩⟩
  · have value : u.regValue .rsi = v.regValue .r12 - 8 := effect.writes.2.2.1
    have source : v.regValue .r12 = s.regValue .rdi + BitVec.ofNat 64 (32-8*k) :=
      (agree.read (n := 64) (r := 12) (by simp)).trans state.source
    rw [value, source]
    have hnat : 32 - 8*k = (24 - 8*k) + 8 := by omega
    rw [hnat, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · exact effect.writes.2.2.2.trans (congrArg (· + 16) rsp)

end P256.Proofs.ReadBe
