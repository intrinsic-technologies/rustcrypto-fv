import P256.Proofs.Nonce.Initialize.Prepare.Buffer
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.ReadBe.Correct

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Read

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

set_option maxRecDepth 2000 in
theorem call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (state : Prepare.CallReady initial s boundary) (rip : s.RIP = 0x107955)
    (bytes : (registerRegion initial .rcx 32).HasBytes initial.external digest) :
    ∃ t, Stage initial t boundary 288 ∧ P256.Proofs.ReadBe.Pre t boundary ∧
      (registerRegion t .rdi 32).HasBytes t.external digest ∧
      (callEffect (fun _ => 0x119090) 0x10795a s).Holds s t := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.stage.toFrameState 0x7955 0x11736
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x19090 (by decide)) rip
  change (callEffect (fun _ => 0x119090) 0x10795a s).Holds s t at effect
  have frame : Stage initial t boundary 288 := by
    obtain ⟨fuel, execution⟩ := state.stage.execution
    exact ⟨state.stage.toFrameState.after_call pre.toCalleePre (by decide) (by decide)
      ready effect, fuel + 1, execution.trans run⟩
  have rsp : stackPtr t = stackPtr initial - 288 := frame.rsp
  have rspn : (stackPtr t).toNat = (stackPtr initial).toNat - 288 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have source : t.regValue .rdi = initial.regValue .rcx :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.inputPointer
  have output : t.regValue .rdx = stackPtr initial - 176 := by
    have h := (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.outputPointer
    change t.regValue .rdx = stackPtr s + 104 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have outputn : (t.regValue .rdx).toNat = (stackPtr initial).toNat - 176 := by
    rw [output]
    exact stack_sub_toNat pre.stack (by decide)
  have ret : (returnBoundary t).rip = 0x10795a := (callEffect_stack effect).1
  have bounds := stack_bounds pre.stack
  have inputRegion : registerRegion t .rdi 32 = registerRegion initial .rcx 32 := by
    simp only [registerRegion, source]
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
  have decoderPre : P256.Proofs.ReadBe.Pre t boundary := by
    refine {
      bindingsSupported := frame.bindingsSupported
      machine := frame.machine
      directionFlag := frame.directionFlag
      loaded := frame.loaded
      rip := effect.rip
      count := (effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans state.count
      limbs := (effect.agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])).trans state.limbs
      bits := (effect.agrees.read (n := 64) (r := 8) (by simp [pushEffect_components])).trans state.requestedBits
      inputBounded := inputRegion.symm ▸ pre.digestBounded
      inputAllocated := ?_
      outputBounded := ?_
      outputAllocated := alloc _ outputSub
      stack := ?_
      separation := ?_
      avoids := ?_
      outerBoundary := pre.outerBoundary
      returnInProgram := ret ▸ inProgram_of_textOffset 0x795a (by decide)
    }
    · rw [inputRegion]
      intro a ha
      exact Option.isSome_iff_exists.mp (frame.allocated a
        (Option.isSome_iff_exists.mpr (pre.digestAllocated a ha)))
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
        exact pre.digestStack a ha (outputSub a hb)
      · intro a ha hb
        rw [inputRegion] at ha
        exact pre.digestStack a ha (stackSub a hb)
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
  rw [inputRegion]
  refine ⟨bytes.1, ?_⟩
  intro i
  have size : digest.size = 32 := bytes.1
  have addressEq : BitVec.ofNat 64 ((registerRegion initial .rcx 32).start + i.val) =
      initial.regValue .rcx + BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add]
    simp only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [addressEq, frame.frame _]
  · simpa only [addressEq] using bytes.2 i
  · intro region member inside
    have inputInside := memoryRegion_contains_add pre.digestBounded (Nat.le_refl _) (Nat.le_refl _)
      (show i.val < 32 by have := i.isLt; omega)
    have alternatives : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
      simpa using member
    rcases alternatives with rfl | rfl
    · exact pre.digestOutput _ inputInside inside
    · exact pre.digestStack _ inputInside inside

end P256.Proofs.Nonce.Initialize.Read
