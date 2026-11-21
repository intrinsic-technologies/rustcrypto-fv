import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (stack_bounds stack_sub_toNat stack_sub_readable
  stack_sub_writable8 readable_of_grow writable_of_grow)

theorem stack_apart_code [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (offset len codeOffset codeLen : Nat)
    (lo : offset ≤ 128) (hi : len ≤ offset) (code : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi' j hj eqn
  apply pre.avoids (Stack.region initial 128) (by simp)
    (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
    (stackRegion_contains_sub pre.stack.2.2.1 lo hi ⟨i, hi', rfl⟩)
  left
  rw [eqn]
  have ip := inProgram_of_textOffset (codeOffset+j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using ip

theorem output_contains [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) {offset len : Nat} (within : offset + len ≤ 32)
    {a : BitVec 64}
    (cover : (Component.mem (initial.regValue .rdx + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion initial .rdx 32).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := cover
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
    (show offset+i < 32 by omega)

theorem copy_pre [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (effect : (callEffect (fun _ => 0x11c930) 0x10708b s).Holds s t)
    (ready : ReadyToStep t) (bound : offset + 8 ≤ 32)
    (source : s.regValue .rsi = stackPtr initial - 56)
    (destination : s.regValue .rdi = initial.regValue .rdx + BitVec.ofNat 64 offset) :
    CalleePre t boundary 0x11c930 8 8 0 := by
  have sp : stackPtr t = stackPtr initial - 80 := by
    have hw : stackPtr t = pushAddr s := effect.writes.1
    rw [hw, pushAddr, stage.rsp, BitVec.sub_sub]
    rfl
  have src : t.regValue .rsi = stackPtr initial - 56 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dst : t.regValue .rdi = initial.regValue .rdx + BitVec.ofNat 64 offset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have bounds := stack_bounds pre.stack
  have sn : (stackPtr t).toNat = (stackPtr initial).toNat - 80 := by
    rw [sp]; exact stack_sub_toNat pre.stack (by decide)
  have rn : (t.regValue .rsi).toNat = (stackPtr initial).toNat - 56 := by
    rw [src]; exact stack_sub_toNat pre.stack (by decide)
  have on : (t.regValue .rdi).toNat = (initial.regValue .rdx).toNat + offset := by
    rw [dst, toNat_add_ofNat]
    have hb := pre.outputBounded
    change (initial.regValue .rdx).toNat + 32 < 2^32 at hb
    omega
  have stackWithin (a : Nat) (h : (Stack.region t 0).Contains a) :
      (Stack.region initial 128).Contains a := by
    change (stackPtr t).toNat - 0 ≤ a ∧ a < (Stack.region t 0).start + (Stack.region t 0).size at h
    rw [stack_region_end, sn] at h
    change (stackPtr initial).toNat - 128 ≤ a ∧
      a < (Stack.region initial 128).start + (Stack.region initial 128).size
    rw [stack_region_end]; omega
  have inputWithin (a : Nat) (h : (registerRegion t .rsi 8).Contains a) :
      (Stack.region initial 128).Contains a := by
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 8 at h
    rw [rn] at h
    change (stackPtr initial).toNat - 128 ≤ a ∧
      a < (Stack.region initial 128).start + (Stack.region initial 128).size
    rw [stack_region_end]; omega
  have outputWithin (a : Nat) (h : (registerRegion t .rdi 8).Contains a) :
      (registerRegion initial .rdx 32).Contains a := by
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 8 at h
    rw [on] at h
    change (initial.regValue .rdx).toNat ≤ a ∧ a < (initial.regValue .rdx).toNat + 32
    omega
  have grow := fun a ha => effect.agrees.grow a (stage.allocated a ha)
  have loaded : ProgramLoaded t := by
    intro a b fetch
    rw [effect.agrees.memory a]
    · exact stage.loaded a b fetch
    · intro c hc cover
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact cover
      · have address : pushAddr s = stackPtr initial - 80 := by
          rw [pushAddr, stage.rsp, BitVec.sub_sub]; rfl
        rw [address] at cover
        exact pre.avoids (Stack.region initial 128) (by simp) a
          (stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) cover) (.inl ⟨b, fetch⟩)
      · exact cover
  refine ⟨bindingsSupported_of_ready_agrees stage.bindingsSupported ready effect.agrees, supportedMachine_of_ready_agrees stage.machine ready effect.agrees,
    effect.agrees.directionFlagClear (by simp) stage.directionFlag, loaded, effect.rip,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, pre.outerBoundary, ?_⟩
  · change (t.regValue .rsi).toNat + 8 < 2^32
    rw [rn]; omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr
      (pre.stack.2.1 a (inputWithin a.toNat ha))))
  · change (t.regValue .rdi).toNat + 8 < 2^32
    rw [on]
    have hb := pre.outputBounded
    change (initial.regValue .rdx).toNat + 32 < 2^32 at hb
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr
      (pre.outputAllocated a (outputWithin a.toNat ha))))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change (Stack.region t 0).start + (Stack.region t 0).size < 2^32
      rw [stack_region_end, sn]; omega
    · intro a ha
      exact Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr
        (pre.stack.2.1 a (stackWithin a.toNat ha))))
    · exact Nat.zero_le _
    · change (stackPtr t).toNat % 16 = 8
      rw [sn]
      have align : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · intro a ha hb
      exact pre.separation (1 : Fin 3) 2 (by decide) a (outputWithin a hb) (inputWithin a ha)
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 8 at ha
      have upper : a < (stackPtr t).toNat + 8 := by
        change (Stack.region t 0).Contains a at hb
        simpa only [stack_region_end] using hb.2
      rw [rn] at ha
      rw [sn] at upper
      omega
    · intro a ha hb
      exact pre.separation (1 : Fin 3) 2 (by decide) a (outputWithin a ha) (stackWithin a hb)
  · intro region member a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputWithin a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackWithin a.toNat ha)
  · change InProgram (stackTop t)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0x708b (by decide)

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
