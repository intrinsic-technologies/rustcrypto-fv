import P256.Proofs.Nonce.Fill.Generate.Copy.Prepare
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

theorem push (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      (callEffect (fun _ => 0x11c930) 0x1073d2 s).Holds s t := by
  have addr := call_address input.toFrame
  have pushPre : PushPre 0x1073d0 2 s := by
    refine ⟨input.rip, ?_, ?_⟩
    · rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
        (by decide) (by decide)) input.allocated
    · rw [addr]
      intro i hi j hj eq
      apply pre.avoids (Stack.region initial 2096) (by simp) _
        (ScalarFrame.stack_contains pre.toCalleePre (offset := 240)
          (by decide) (by decide) ⟨i, hi, rfl⟩) (.inl ?_)
      change InProgram (stackPtr initial - 240 + BitVec.ofNat 64 i)
      rw [eq]
      have h := inProgram_of_textOffset (0x73d0 + j) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
      exact h
  obtain ⟨t, run, ready, effect⟩ :=
    (call_r64_effect_step 0x1073d0 0xd3 rfl rfl).advances
      (readyToStep input.machine input.bindingsSupported)
      (programText_slice (programLoaded_codeIn input.loaded) 0x73d0 _
        (by decide) (by decide +kernel))
      ⟨pushPre, by change (s.regValue .rbx).toNat < 2^32; rw [input.rbx]; decide⟩
      (by change s.regValue .rbx ≠ boundary.rip; rw [input.rbx]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide)))
  refine ⟨t, run, ready, ?_⟩
  change (callEffect (fun q => q.regValue .rbx) 0x1073d2 s).Holds s t at effect
  simpa only [callEffect, pushEffect, input.rbx] using effect

theorem value_address (pre : Pre initial boundary orderAddress original) :
    (initial.regValue .rdi + 40).toNat = (initial.regValue .rdi).toNat + 40 := by
  have bound : (initial.regValue .rdi).toNat + 72 < 2^32 := pre.outputBounded
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by change (initial.regValue .rdi).toNat + 40 < 2^64; omega)

theorem value_sub (pre : Pre initial boundary orderAddress original) {a : Nat}
    (inside : (MemoryRegion.mk (initial.regValue .rdi + 40).toNat 32).Contains a) :
    (registerRegion initial .rdi 72).Contains a := by
  change (initial.regValue .rdi + 40).toNat ≤ a ∧ a < (initial.regValue .rdi + 40).toNat + 32 at inside
  rw [value_address pre] at inside
  change (initial.regValue .rdi).toNat ≤ a ∧ a < (initial.regValue .rdi).toNat + 72
  constructor <;> omega

theorem call_pre (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => 0x11c930) 0x1073d2 s).Holds s t) :
    CalleePre t boundary 0x11c930 32 32 0 := by
  have bounds := stack_bounds pre.stack
  have rsp : stackPtr t = stackPtr initial - 240 :=
    effect.writes.1.trans (call_address input.toFrame)
  have sp : (stackPtr t).toNat = (stackPtr initial).toNat - 240 := by
    rw [rsp]; exact stack_sub_toNat pre.stack (by decide)
  have output : t.regValue .rdi = initial.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.rdi
  have source : t.regValue .rsi = initial.regValue .rdi + 40 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input.rsi
  have sub : ∀ a, (registerRegion t .rsi 32).Contains a →
      (registerRegion initial .rdi 72).Contains a := by
    intro a ha
    apply value_sub pre
    simpa only [registerRegion, source] using ha
  have outEq : registerRegion t .rdi 32 = registerRegion initial .rsi 32 := by
    simp only [registerRegion, output]
  have stackSub : ∀ a, (Stack.region t 0).Contains a → (Stack.region initial 2096).Contains a := by
    intro a ha
    change (stackPtr t).toNat - 0 ≤ a ∧ a < (Stack.region t 0).start + (Stack.region t 0).size at ha
    rw [stack_region_end, sp] at ha
    change (stackPtr initial).toNat - 2096 ≤ a ∧ a < (Stack.region initial 2096).start + _
    rw [stack_region_end]
    constructor <;> omega
  have grow (a : BitVec 64) (ha : ∃ b, initial.external[a]? = some b) :
      ∃ b, t.external[a]? = some b :=
    Option.isSome_iff_exists.mp
      (effect.agrees.grow a (input.allocated a (Option.isSome_iff_exists.mpr ha)))
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees input.bindingsSupported ready effect.agrees
    machine := supportedMachine_of_ready_agrees input.machine ready effect.agrees
    directionFlag := effect.agrees.directionFlagClear (by simp) input.directionFlag
    loaded := call_loaded pre input.toFrame effect
    rip := effect.rip
    inputBounded := ?_
    inputAllocated := fun a ha => grow a (pre.outputAllocated a (sub a.toNat ha))
    outputBounded := by rw [outEq]; exact pre.inputBounded
    outputAllocated := by rw [outEq]; exact fun a ha => grow a (pre.inputAllocated a ha)
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := by
      change InProgram (stackTop t)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0x73d2 (by decide)
  }
  · change (t.regValue .rsi).toNat + 32 < 2^32
    rw [source, value_address pre]
    have h : (initial.regValue .rdi).toNat + 72 < 2^32 := pre.outputBounded
    omega
  · refine ⟨?_, fun a ha => grow a (pre.stack.2.1 a (stackSub a.toNat ha)), ?_, ?_⟩
    · change (Stack.region t 0).start + (Stack.region t 0).size < 2^32
      rw [stack_region_end, sp]; omega
    · exact Nat.zero_le _
    · change (stackPtr t).toNat % 16 = 8
      rw [sp]
      have hm : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j neq a ha hb
    have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
      omega
    rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact pre.separation 0 1 (by decide) a (outEq ▸ hb) (sub a ha)
    · exact pre.separation 1 2 (by decide) a (sub a ha) (stackSub a hb)
    · exact pre.separation 0 2 (by decide) a (outEq ▸ ha) (stackSub a hb)
  · intro r hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.outputAvoids a (outEq ▸ ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)

end P256.Proofs.Nonce.Fill.Generate.Copy
