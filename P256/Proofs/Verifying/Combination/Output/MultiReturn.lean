import P256.Proofs.Verifying.Combination.Loop.MultiPrologue
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Projective.Preserve
import P256.Proofs.Common.Instructions.RepMovsqAny
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import P256.Proofs.Projective.Add.Frame.Restore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open P256.Proofs.Projective.Add (restore_registers restoreComponents)
open P256.Proofs.Common.Field (AdvanceTriple)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  CalleePre s boundary 0x10efd0 48 96 1432

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f301
  readable : MemReadable s (stackPtr s + 16) 8

def setupBytes : List UInt8 :=
  [0x48, 0x8d, 0x74, 0x24, 0x48,
    0xb9, 0x0c, 0, 0, 0, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0xc7]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10f313
    writes := [⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 72⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64).read s⟩] }

theorem setup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x10f301 setupBytes)
      (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f301 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xf306 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10f306 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10f301 setupBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf30b (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x10f30b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f301 setupBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf310 (by decide))⟩
    x86_norm
    exact hP.readable
  advance_then (mov_r64_r64_effect_step 0x10f310 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f301 setupBytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf313 (by decide))⟩
  advance_finish [setupEffect]


def transferComponents (s : RamState) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (s.regValue .rdi) 96, .rip]

theorem transfer [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : State s t)
    (rip : t.RIP = 0x10f313) (src : t.regValue .rsi = stackPtr s - 336)
    (dst : t.regValue .rdi = s.regValue .rdi) (count : t.regValue .rcx = 12)
    (value : ProjectiveAt t (stackPtr s - 336) point) :
    ∃ u, Advances boundary 12 t u ∧ State s u ∧ u.RIP = 0x10f316 ∧
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
    simpa only [BitVec.add_zero] using (output_writable pre (by decide) state.allocated).add 0 (len := 96) (by decide)
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
    · change (stackPtr s).toNat - 1432 ≤ address ∧
        address < (Stack.region s 1432).start + (Stack.region s 1432).size
      rw [stack_region_end]
      dsimp only [address]
      constructor <;> omega
  have apart : RangeApart (rdi.read t) 96 0x10f313 3 := by
    change RangeApart (t.regValue .rdi) 96 0x10f313#64 3
    rw [dst]
    have ha := P256.Proofs.Common.Instructions.RangeApart.add_left (h := (output_code pre (offset := 0xf313) (len := 3) (by decide)))
      0 (len := 96) (by decide)
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using ha
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf313 [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf313 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf316 (by decide)))
  simp only [show max 12 1 = 12 from rfl] at run ready effect bytes
  generalize hu : nextStates 12 t = u at run ready effect bytes
  have frame : AgreesExcept (transferComponents s) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = s.regValue .rdi from dst,
      Nat.reduceMul, transferComponents] using effect.agrees
  have writes : WritesWithin (transferComponents s) #v[registerRegion s .rdi 96, workRegion s 1432] := by
    intro c hc a ha
    simp only [transferComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨registerRegion s .rdi 96, by simp,
      memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show i < 96 by omega)⟩
  refine ⟨u, run, FrameState.after_effect pre (by decide) state ready frame writes (by simp [transferComponents]), effect.rip, ?_, frame⟩
  apply value.of_bytes_eq
  intro i hi
  have hb := bytes i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb


def epilogueComponents : List Component := .flags :: restoreComponents

theorem epilogue_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (state : FrameState s t 96 1432 408) (rip : t.RIP = 0x10f316) :
    ∃ u, Advances boundary 8 t u ∧ ReadyToStep u ∧
      AgreesExcept epilogueComponents t u ∧
      u.RIP = (returnBoundary s).rip ∧ stackPtr u = (returnBoundary s).rsp ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = s.regValue r) := by
  obtain ⟨v, step, ready, effect⟩ :=
    (add_r64_imm32_effect_step 0x10f316 0x48 0xc4 360
      (by constructor <;> decide) (by decide) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf316
        [0x48, 0x81, 0xc4, 0x68, 0x01, 0, 0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf31d (by decide)))
  change (addR64Imm32Effect 0x10f316 4 360 t).Holds t v at effect
  have memory : v.external = t.external := effect.agrees.external (by simp [Component.Covers])
  have restore : FrameState s v 96 1432 48 := by
    refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
      supportedMachine_of_ready_agrees state.machine ready effect.agrees, ?_,
      effect.agrees.directionFlagClear (by component_not_mem) state.directionFlag,
      fun a ha => effect.agrees.grow a (state.allocated a ha), ?_, ?_, ?_, ?_,
      (effect.agrees.mxcsr (by component_not_mem)).trans state.mxcsr,
      (effect.agrees.fcw (by component_not_mem)).trans state.fp87⟩
    · intro a b hb
      rw [memory]
      exact state.loaded a b hb
    · intro a ha
      rw [memory]
      exact state.frame a ha
    · have hw : stackPtr v = stackPtr t + 360 := effect.writes
      rw [hw, state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro item hi
      rw [memory]
      exact state.saved item hi
    · change memLoad v.external (stackPtr s) 64 = _
      rw [memory]
      exact state.returnAddress
  obtain ⟨u, run, ready', frame, rip', rsp', regs⟩ :=
    restore_registers pre (by decide) restore (codeOffset := 0xf31d)
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ effect.rip
  refine ⟨u, step.trans run, ready', ?_, rip', rsp', regs⟩
  apply (effect.agrees.trans frame).mono
  simp [epilogueComponents, restoreComponents]

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (state : FrameState s t 96 1432 408) (rip : t.RIP = 0x10f316)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 96 1432 ∧ u.external = t.external := by
  obtain ⟨u, run, ready, frame, rip', rsp', regs⟩ := epilogue_correct pre state rip
  have memory : u.external = t.external :=
    frame.external (by simp [epilogueComponents, restoreComponents, Component.Covers])
  refine ⟨u, ⟨?_, rip', rsp',
    bindingsSupported_of_ready_agrees state.bindingsSupported ready frame,
    supportedMachine_of_ready_agrees state.machine ready frame,
    regs, frame.directionFlagClear (by component_not_mem) state.directionFlag,
    (frame.mxcsr (by component_not_mem)).trans state.mxcsr,
    (frame.fcw (by component_not_mem)).trans state.fp87,
    ?_, ?_, fun a ha => frame.grow a (state.allocated a ha)⟩, memory⟩
  · obtain ⟨fuel, execution⟩ := execution
    exact ⟨fuel + 8, execution.trans run⟩
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb


theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x10f301)
    (value : ProjectiveAt t (stackPtr s - 336) point)
    (output : (Operand.mem (stackPtr s - 392) : Operand 64).read t = s.regValue .rdi)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 96 1432 ∧ ProjectiveAt u (s.regValue .rdi) point := by
  obtain ⟨n, a, run, ready, _, effect⟩ := setup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf301 setupBytes
      (by decide) (by decide +kernel))
    ⟨rip, stack_readable pre state (offset := 16) (len := 8) (by decide) (by decide)⟩
  have frame : AgreesExcept [.reg 6, .reg 1, .reg 0, .reg 7, .rip] t a := effect.agrees
  have memory : a.external = t.external := frame.external (by simp [Component.Covers])
  have stateA := state.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have writes : a.regValue .rsi = stackPtr t + 72 ∧ a.regValue .rcx = 12 ∧
      a.regValue .rax = (Operand.mem (stackPtr t + 16) : Operand 64).read t ∧
      a.regValue .rdi = (Operand.mem (stackPtr t + 16) : Operand 64).read t := effect.writes
  have src : a.regValue .rsi = stackPtr s - 336 :=
    writes.1.trans (scalar_stack_address state.rsp (offset := 72) (by decide) (by decide))
  have dst : a.regValue .rdi = s.regValue .rdi := by
    rw [writes.2.2.2]
    change (Operand.mem (stackPtr t + BitVec.ofNat 64 16) : Operand 64).read t = _
    rw [scalar_stack_address state.rsp (offset := 16) (by decide) (by decide)]
    exact output
  have pointA : ProjectiveAt a (stackPtr s - 336) point :=
    value.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) memory)
  obtain ⟨b, runB, stateB, ripB, pointB, _⟩ :=
    transfer pre stateA effect.rip src dst writes.2.1 pointA
  obtain ⟨fuel, runS⟩ := execution
  obtain ⟨u, result, memoryU⟩ := epilogue pre stateB ripB
    ⟨fuel + n + 12, (runS.trans run).trans runB⟩
  exact ⟨u, result, pointB.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) memoryU)⟩


end P256.Proofs.Verifying.Combination.Loop.Multi.Return
