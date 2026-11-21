import P256.Proofs.Nonce.Initialize.Seed.PrepareUpdate
import P256.Proofs.Nonce.Update.Interface
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {secret : Nat} {value : Nat}

theorem update_pre (pre : Nonce.InitializePre initial boundary orderAddress)
    (state : UpdateReady initial s boundary orderAddress value)
    (key : (registerRegion initial .rsi 32).HasBytes initial.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret))
    (run : Advances boundary 1 s t) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => 0x109f30) 0x107c1a s).Holds s t) :
    UpdateSeededPre t boundary ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret)
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n value) := by
  have stage : Stage initial t boundary 288 := by
    obtain ⟨fuel, execution⟩ := state.stage.execution
    exact ⟨state.stage.toFrameState.after_call pre.toCalleePre (by decide) (by decide)
      ready effect, fuel + 1, execution.trans run⟩
  have bounds := stack_bounds pre.stack
  have sn : (stackPtr s).toNat = (stackPtr initial).toNat - 280 := by
    rw [state.stage.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have tn : (stackPtr t).toNat = (stackPtr initial).toNat - 288 := by
    rw [stage.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have localNat (offset : Nat) (bound : offset ≤ 280) :
      (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr initial).toNat - 280 + offset := by
    rw [HMAC.Finalize.stack_address (depth := 280) state.stage.rsp bound,
      stack_sub_toNat pre.stack (by omega)]
    omega
  have localBound (offset count : Nat) (bound : offset + count ≤ 280) :
      (MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 offset).toNat count).Bounded := by
    change (stackPtr s + BitVec.ofNat 64 offset).toNat + count < 2^32
    rw [localNat offset (by omega)]
    omega
  have localSub (offset count : Nat) (bound : offset + count ≤ 280) :
      ∀ a, (MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 offset).toNat count).Contains a →
        (Stack.region initial 2144).Contains a := by
    intro a ha
    change (stackPtr s + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 offset).toNat + count at ha
    rw [localNat offset (by omega)] at ha
    change (stackPtr initial).toNat - 2144 ≤ a ∧
      a < (Stack.region initial 2144).start + (Stack.region initial 2144).size
    rw [stack_region_end]
    constructor <;> omega
  have localAllocated (offset count : Nat) (bound : offset + count ≤ 280) :
      (MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 offset).toNat count).Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (stage.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (localSub offset count bound a.toNat ha))))
  have hdi : t.regValue .rdi = stackPtr s + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.destination
  have hsi : t.regValue .rsi = stackPtr s + 104 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans state.descriptors
  have hdin : (t.regValue .rdi).toNat = (stackPtr initial).toNat - 280 + 8 := by
    rw [hdi]
    exact localNat 8 (by decide)
  have di : t.regValue .rdi = stackPtr initial - 272 := by
    rw [hdi, state.stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have descriptors : t.regValue .rsi = stackPtr initial - 176 := by
    rw [hsi, state.stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  let layout : StackCallLayout 2144 48 64 1856 :=
    ⟨288, 176, 272, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  have ret : (returnBoundary t).rip = 0x107c1a := (callEffect_stack effect).1
  have cp := CalleePre.of_stack pre.toCalleePre layout stage.bindingsSupported stage.machine
    stage.directionFlag stage.loaded stage.allocated effect.rip stage.rsp descriptors di
    (ret ▸ inProgram_of_textOffset 0x7c1a (by decide))
  have stateSub : ∀ a, (registerRegion t .rdi 64).Contains a →
      (Stack.region initial 2144).Contains a := by
    simpa only [registerRegion, hdi, BitVec.ofNat_eq_ofNat] using localSub 8 64 (by decide)
  have stackSub : ∀ a, (Stack.region t 1856).Contains a →
      (Stack.region initial 2144).Contains a := by
    intro a ha
    change (stackPtr t).toNat - 1856 ≤ a ∧ a < (Stack.region t 1856).start + (Stack.region t 1856).size at ha
    rw [stack_region_end, tn] at ha
    change (stackPtr initial).toNat - 2144 ≤ a ∧ a < (Stack.region initial 2144).start + (Stack.region initial 2144).size
    rw [stack_region_end]
    constructor <;> omega
  have localStateApart (offset count : Nat) (lo : 104 ≤ offset) (hi : offset + count ≤ 280) :
      (MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 offset).toNat count).Disjoint
        (registerRegion t .rdi 64) := by
    intro a ha hb
    have low := ha.1
    have high := hb.2
    change (stackPtr s + BitVec.ofNat 64 offset).toNat ≤ a at low
    change a < (t.regValue .rdi).toNat + 64 at high
    rw [localNat offset (by omega)] at low
    rw [hdin] at high
    omega
  have localStackApart (offset count : Nat) (hi : offset + count ≤ 280) :
      (MemoryRegion.mk (stackPtr s + BitVec.ofNat 64 offset).toNat count).Disjoint
        (Stack.region t 1856) := by
    intro a ha hb
    have low := ha.1
    have high := hb.2
    change (stackPtr s + BitVec.ofNat 64 offset).toNat ≤ a at low
    rw [localNat offset (by omega)] at low
    rw [stack_region_end, tn] at high
    omega
  have copied (offset count : Nat) (bound : offset + count ≤ 280) :
      ∀ i < count, t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
    (fun i hi => by
      have addr : stackPtr s + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (280-offset) :=
        HMAC.Finalize.stack_address (depth := 280) state.stage.rsp (by omega)
      rw [addr]
      exact ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide) state.stage.toFrameState
        effect (offset := 280-offset) (len := count) (by omega) (by omega) hi)
  have load (offset : Nat) (bound : offset + 8 ≤ 280) :
      loadBytes t.external (stackPtr s + BitVec.ofNat 64 offset) 8 =
        .ok (memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64) := by
    have readable := ScalarFrame.stack_readable (frameOffset := 280) pre.toCalleePre state.stage.toFrameState (offset := offset) (len := 8) (by omega) (by omega)
    have bytes := (Bytes.of_memLoad (n := 64) (fun i hi =>
      effect.agrees.grow _ (readable.mem i hi))).loadBytes64
    rw [word_of_copied (copied offset 8 bound)] at bytes
    exact bytes
  have keySize : (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret).size = 32 := key.1
  have reducedSize : (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n value).size = 32 := state.octets.1
  refine {
    toDrbgCalleePre := {
      bindingsSupported := cp.bindingsSupported
      machine := cp.machine
      directionFlag := cp.directionFlag
      loaded := cp.loaded
      rip := cp.rip
      stateBounded := cp.outputBounded
      stateAllocated := cp.outputAllocated
      stack := cp.stack
      separation := cp.separation 1 2 (by decide)
      avoids := fun region hr => cp.avoids region (by simpa using hr)
      outerBoundary := cp.outerBoundary
      returnInProgram := cp.returnInProgram
      stateBytes := by rw [hdi]; exact state.drbg.copy (copied 8 64 (by decide)) }
    secretSize := keySize
    reducedSize := reducedSize
    inputCount := (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.count
    descriptorsBounded := ?_
    descriptorsAllocated := ?_
    descriptorsStateApart := ?_
    descriptorsStackApart := ?_
    seeds := ?_
  }
  · simpa only [BitVec.ofNat_eq_ofNat, registerRegion, hsi] using localBound 104 48 (by decide)
  · simpa only [BitVec.ofNat_eq_ofNat, registerRegion, hsi] using localAllocated 104 48 (by decide)
  · simpa only [BitVec.ofNat_eq_ofNat, registerRegion, hsi] using localStateApart 104 48 (by decide) (by decide)
  · simpa only [BitVec.ofNat_eq_ofNat, registerRegion, hsi] using localStackApart 104 48 (by decide)
  · refine ⟨initial.regValue .rsi, stackPtr s + 200, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [BitVec.ofNat_eq_ofNat, hsi] using (load 104 (by decide)).trans (congrArg Except.ok state.secretPointer)
    · simpa only [BitVec.ofNat_eq_ofNat, hsi, BitVec.add_assoc, BitVec.reduceAdd] using (load 112 (by decide)).trans (congrArg Except.ok state.secretLength)
    · simpa only [BitVec.ofNat_eq_ofNat, hsi, BitVec.add_assoc, BitVec.reduceAdd] using (load 120 (by decide)).trans (congrArg Except.ok state.reducedPointer)
    · simpa only [BitVec.ofNat_eq_ofNat, hsi, BitVec.add_assoc, BitVec.reduceAdd] using (load 128 (by decide)).trans (congrArg Except.ok state.reducedLength)
    · simpa only [BitVec.ofNat_eq_ofNat, hsi, BitVec.add_assoc, BitVec.reduceAdd] using (load 144 (by decide)).trans (congrArg Except.ok state.entropyLength)
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [keySize, registerRegion] using pre.inputBounded
      · rw [keySize]
        intro a ha
        exact Option.isSome_iff_exists.mp (stage.allocated a
          (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))
      · rw [keySize]
        apply hasBytes_copy key
        intro i hi
        apply frame_read stage.frame (address := initial.regValue .rsi + BitVec.ofNat 64 i) _
          (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
        intro region hr
        have cases : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
          simpa using hr
        rcases cases with rfl | rfl
        · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide)
        · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)
      · rw [keySize]
        intro a hi ho
        exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a hi (stateSub a ho)
      · rw [keySize]
        intro a hi hs
        exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a hi (stackSub a hs)
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [BitVec.ofNat_eq_ofNat, reducedSize] using localBound 200 32 (by decide)
      · simpa only [BitVec.ofNat_eq_ofNat, reducedSize] using localAllocated 200 32 (by decide)
      · rw [reducedSize]
        exact hasBytes_copy state.octets (copied 200 32 (by decide))
      · simpa only [BitVec.ofNat_eq_ofNat, reducedSize] using localStateApart 200 32 (by decide) (by decide)
      · simpa only [BitVec.ofNat_eq_ofNat, reducedSize] using localStackApart 200 32 (by decide)

end P256.Proofs.Nonce.Initialize.Seed
