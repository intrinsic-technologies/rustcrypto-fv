import P256.Proofs.Nonce.Fill.Tail.Decode.Read.State
import P256.Proofs.Nonce.Fill.Call
import P256.Proofs.ReadBe.Correct

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Read

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state) :
    ∃ t, Advances boundary 1 s t ∧
      (callEffect (fun _ => 0x119090) 0x107528 s).Holds s t ∧
      P256.Proofs.ReadBe.Pre t boundary ∧
      (registerRegion t .rdi 32).HasBytes t.external (updateValue state).value := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 232) (by decide) (by decide)
    (readyToStep input.machine input.bindingsSupported) input.loaded input.allocated input.rsp
    0x7523 0x11b68 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x19090 (by decide)) input.rip
  change (callEffect (fun _ => 0x119090) 0x107528 s).Holds s t at effect
  have grow (a : BitVec 64) (ha : (initial.external[a]?).isSome) : (t.external[a]?).isSome :=
    effect.agrees.grow a (input.allocated a ha)
  have rsp : stackPtr t = stackPtr initial - 240 := effect.writes.1.trans (call_address input.toFrame)
  have rspn : (stackPtr t).toNat = (stackPtr initial).toNat - 240 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have source : t.regValue .rdi = initial.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans input.source
  have output : t.regValue .rdx = stackPtr initial - 128 :=
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans input.destination).trans
      (frameBase_add initial (offset := 104) (by decide))
  have outputn : (t.regValue .rdx).toNat = (stackPtr initial).toNat - 128 := by
    rw [output]
    exact stack_sub_toNat pre.stack (by decide)
  have ret : (returnBoundary t).rip = 0x107528 := (callEffect_stack effect).1
  have bounds := stack_bounds pre.stack
  have inputRegion : registerRegion t .rdi 32 = registerRegion initial .rsi 32 := by
    simp only [registerRegion, source]
  have stackStart : (Stack.region t 128).start = (stackPtr initial).toNat - 368 := by
    change (stackPtr t).toNat - 128 = _
    rw [rspn]
    omega
  have stackEnd : (Stack.region t 128).start + (Stack.region t 128).size =
      (stackPtr initial).toNat - 232 := by
    rw [stack_region_end, rspn]
    omega
  have outputSub (a : Nat) (ha : (registerRegion t .rdx 32).Contains a) :
      (Stack.region initial 2096).Contains a := by
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    rw [outputn] at ha
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
    rw [stack_region_end]
    omega
  have stackSub (a : Nat) (ha : (Stack.region t 128).Contains a) :
      (Stack.region initial 2096).Contains a := by
    change (Stack.region t 128).start ≤ a ∧
      a < (Stack.region t 128).start + (Stack.region t 128).size at ha
    rw [stackEnd, stackStart] at ha
    change (stackPtr initial).toNat - 2096 ≤ a ∧
      a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
    rw [stack_region_end]
    exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide : 368 ≤ 2096) _) ha.1,
      Nat.lt_of_lt_of_le ha.2 (Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _))⟩
  have alloc (r : MemoryRegion) (sub : ∀ a, r.Contains a → (Stack.region initial 2096).Contains a) :
      r.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (sub a.toNat ha))))
  have decoderPre : P256.Proofs.ReadBe.Pre t boundary := by
    refine {
      bindingsSupported := bindingsSupported_of_ready_agrees input.bindingsSupported ready effect.agrees
      machine := supportedMachine_of_ready_agrees input.machine ready effect.agrees
      directionFlag := effect.agrees.directionFlagClear (by simp) input.directionFlag
      loaded := call_loaded pre input.toFrame effect
      rip := effect.rip
      count := (effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans input.count
      limbs := (effect.agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])).trans input.limbs
      bits := (effect.agrees.read (n := 64) (r := 8) (by simp [pushEffect_components])).trans input.bits
      inputBounded := inputRegion.symm ▸ pre.inputBounded
      inputAllocated := ?_
      outputBounded := ?_
      outputAllocated := alloc _ outputSub
      stack := ?_
      separation := ?_
      avoids := ?_
      outerBoundary := pre.outerBoundary
      returnInProgram := ret ▸ inProgram_of_textOffset 0x7528 (by decide)
    }
    · rw [inputRegion]
      intro a ha
      exact Option.isSome_iff_exists.mp (grow a
        (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))
    · change (t.regValue .rdx).toNat + 32 < 2^32
      rw [outputn]
      omega
    · refine ⟨?_, alloc _ stackSub, ?_, ?_⟩
      · change (Stack.region t 128).start + (Stack.region t 128).size < 2^32
        rw [stackEnd]
        omega
      · change 128 ≤ (stackPtr t).toNat
        rw [rspn]
        omega
      · change (stackPtr t).toNat % 16 = 8
        rw [rspn]
        have aligned : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
        omega
    · intro i j hij
      have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
      rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · intro a ha hb
        rw [inputRegion] at ha
        exact pre.separation 0 2 (by decide) a ha (outputSub a hb)
      · intro a ha hb
        rw [inputRegion] at ha
        exact pre.separation 0 2 (by decide) a ha (stackSub a hb)
      · intro a ha hb
        change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
        change (Stack.region t 128).start ≤ a ∧
          a < (Stack.region t 128).start + (Stack.region t 128).size at hb
        rw [outputn] at ha
        rw [stackEnd] at hb
        omega
    · intro r hr a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact pre.avoids _ (by simp) a (outputSub a.toNat ha)
      · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)
  refine ⟨t, run, effect, decoderPre, ?_⟩
  rw [inputRegion]
  apply frame_hasBytes (effect.agrees.memoryWriteFrame (call_writes pre input.toFrame))
    _ pre.inputBounded input.output
  intro region member
  have eq : region = Stack.region initial 2096 := by simpa using member
  subst region
  exact pre.separation 0 2 (by decide)

end P256.Proofs.Nonce.Fill.Tail.Decode.Read
