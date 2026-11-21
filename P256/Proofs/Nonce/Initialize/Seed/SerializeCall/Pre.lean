import P256.Proofs.Nonce.Initialize.Seed.SerializeCall.Setup
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar

set_option maxRecDepth 2000 in
theorem serialization_call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {value : Nat}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (state : SerializationReady initial s boundary orderAddress value) :
    ∃ t, Stage initial t boundary 288 ∧ Conversions.Int2Octets.Pre t boundary ∧
      Nat256At t (t.regValue .rdi) value ∧
      (callEffect (fun _ => 0x106f40) 0x107b85 s).Holds s t := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.stage.toFrameState 0x7b80 0xfffff3bb
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x6f40 (by decide)) state.rip
  change (callEffect (fun _ => 0x106f40) 0x107b85 s).Holds s t at effect
  have frame : Stage initial t boundary 288 := by
    obtain ⟨fuel, execution⟩ := state.stage.execution
    exact ⟨state.stage.toFrameState.after_call pre.toCalleePre (by decide) (by decide)
      ready effect, fuel + 1, execution.trans run⟩
  have rsp : stackPtr t = stackPtr initial - 288 := frame.rsp
  have rspn : (stackPtr t).toNat = (stackPtr initial).toNat - 288 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have source : t.regValue .rdi = stackPtr initial - 272 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.source
    change t.regValue .rdi = stackPtr s + 8 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have sourcen : (t.regValue .rdi).toNat = (stackPtr initial).toNat - 272 := by
    rw [source]
    exact stack_sub_toNat pre.stack (by decide)
  have order : t.regValue .rsi = orderAddress :=
    (effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans state.orderArg
  have output : t.regValue .rdx = stackPtr initial - 80 := by
    have h := (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.destination
    change t.regValue .rdx = stackPtr s + 200 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have outputn : (t.regValue .rdx).toNat = (stackPtr initial).toNat - 80 := by
    rw [output]
    exact stack_sub_toNat pre.stack (by decide)
  have ret : (returnBoundary t).rip = 0x107b85 := (callEffect_stack effect).1
  have bounds := stack_bounds pre.stack
  have stackStart : (Stack.region t 128).start = (stackPtr initial).toNat - 416 := by
    change (stackPtr t).toNat - 128 = _
    rw [rspn]
    omega
  have stackEnd : (Stack.region t 128).start + (Stack.region t 128).size =
      (stackPtr initial).toNat - 280 := by
    rw [stack_region_end, rspn]
    omega
  have outputSub (a : Nat) (ha : (registerRegion t .rdx 32).Contains a) :
      (Stack.region initial 2144).Contains a := by
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    rw [outputn] at ha
    change (stackPtr initial).toNat - 2144 ≤ a ∧
      a < (Stack.region initial 2144).start + (Stack.region initial 2144).size
    rw [stack_region_end]
    omega
  have inputSub (a : Nat) (ha : (registerRegion t .rdi 32).Contains a) :
      (Stack.region initial 2144).Contains a := by
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
    rw [sourcen] at ha
    change (stackPtr initial).toNat - 2144 ≤ a ∧
      a < (Stack.region initial 2144).start + (Stack.region initial 2144).size
    rw [stack_region_end]
    omega
  have stackSub (a : Nat) (ha : (Stack.region t 128).Contains a) :
      (Stack.region initial 2144).Contains a := by
    change (Stack.region t 128).start ≤ a ∧
      a < (Stack.region t 128).start + (Stack.region t 128).size at ha
    rw [stackEnd, stackStart] at ha
    change (stackPtr initial).toNat - 2144 ≤ a ∧
      a < (Stack.region initial 2144).start + (Stack.region initial 2144).size
    rw [stack_region_end]
    omega
  have alloc (r : MemoryRegion) (sub : ∀ a, r.Contains a → (Stack.region initial 2144).Contains a) :
      r.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (frame.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (sub a.toNat ha))))
  have decoderPre : Conversions.Int2Octets.Pre t boundary := by
    refine {
      bindingsSupported := frame.bindingsSupported
      machine := frame.machine
      directionFlag := frame.directionFlag
      loaded := frame.loaded
      rip := effect.rip
      length := (effect.agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])).trans state.count
      inputBounded := by change (t.regValue .rdi).toNat + 32 < 2^32; rw [sourcen]; omega
      inputAllocated := alloc _ inputSub
      orderBounded := by simpa only [registerRegion, order] using pre.orderBounded
      orderAllocated := by
        intro a ha
        have h := pre.orderAllocated a (by simpa only [registerRegion, order] using ha)
        exact Option.isSome_iff_exists.mp (frame.allocated a (Option.isSome_iff_exists.mpr h))
      orderOutput := by
        intro a ha hb
        exact pre.orderStack a (by simpa only [registerRegion, order] using ha) (outputSub a hb)
      orderStack := by
        intro a ha hb
        exact pre.orderStack a (by simpa only [registerRegion, order] using ha) (stackSub a hb)
      order := by
        rw [order]
        refine ⟨pre.order.1, ?_⟩
        intro i hi
        rw [frame.frame _]
        · exact pre.order.2 i hi
        · intro region member inside
          have hin := memoryRegion_contains_add pre.orderBounded (Nat.le_refl _) (Nat.le_refl _) hi
          have cases : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
            simpa using member
          rcases cases with rfl | rfl
          · exact pre.orderOutput _ hin inside
          · exact pre.orderStack _ hin inside
      outputBounded := ?_
      outputAllocated := alloc _ outputSub
      stack := ?_
      separation := ?_
      avoids := ?_
      outerBoundary := pre.outerBoundary
      returnInProgram := ret ▸ inProgram_of_textOffset 0x7b85 (by decide)
    }
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
        change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
        change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at hb
        rw [sourcen] at ha
        rw [outputn] at hb
        omega
      · intro a ha hb
        change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at ha
        have hb' := hb.2
        change a < (Stack.region t 128).start + (Stack.region t 128).size at hb'
        rw [sourcen] at ha
        rw [stackEnd] at hb'
        omega
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
  refine ⟨t, frame, decoderPre, ?_, effect⟩
  rw [source]
  refine ⟨state.reduced.1, ?_⟩
  intro i hi
  have address : stackPtr s + 8 = stackPtr initial - 272 := by
    rw [state.stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v := state.reduced.2 i hi
  rw [address] at v
  exact (ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide) state.stage.toFrameState
    effect (offset := 272) (len := 32) (by decide) (by decide) hi).trans v

end P256.Proofs.Nonce.Initialize.Seed
