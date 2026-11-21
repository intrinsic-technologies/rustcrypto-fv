import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.CopyPre

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (stack_bounds stack_sub_toNat stack_sub_writable8 writable_of_grow)

def copyFrame (initial : RamState) (offset : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .flags, .rip,
   .mem (stackPtr initial - 80) 8, .mem (initial.regValue .rdx + BitVec.ofNat 64 offset) 8]

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {offset : Nat}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (bound : offset + 8 ≤ 32) (rip : s.RIP = 0x107085)
    (source : s.regValue .rsi = stackPtr initial - 56)
    (destination : s.regValue .rdi = initial.regValue .rdx + BitVec.ofNat 64 offset)
    (count : s.regValue .rdx = 8) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x10708b ∧
      AgreesExcept (copyFrame initial offset) s t ∧
      (∀ j < 8, t.external[initial.regValue .rdx + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? =
        s.external[stackPtr initial - 56 + BitVec.ofNat 64 j]?) := by
  have pointer := P256.Proofs.Program.memcpy_pointer stage.loaded
  have target : callMemPtr 0x107085 (.rip 0xfd46d) s = 0x11c930 := pointer.2
  have address : pushAddr s = stackPtr initial - 80 := by
    rw [pushAddr, stage.rsp, BitVec.sub_sub]; rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by decide) (by decide)) stage.allocated
  have apart : RangeApart (pushAddr s) 8 0x107085 6 := by
    rw [address]
    exact stack_apart_code pre 80 8 0x7085 6 (by decide) (by decide) (by decide)
  obtain ⟨call, run, ready, raw⟩ :=
    (call_m64_effect_step 0x107085 (.rip 0xfd46d) trivial rfl rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7085 _ (by decide) (by decide +kernel))
      ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide⟩, pointer.1⟩
      (by change callMemPtr 0x107085 (.rip 0xfd46d) s ≠ boundary.rip
          rw [target]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide)))
  have effect : (callEffect (fun _ => 0x11c930) 0x10708b s).Holds s call := by
    change (callEffect (callMemPtr 0x107085 (.rip 0xfd46d)) 0x10708b s).Holds s call at raw
    simpa only [callEffect, pushEffect, target] using raw
  have callPre := copy_pre pre stage effect ready bound source destination
  have src : call.regValue .rsi = stackPtr initial - 56 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dst : call.regValue .rdi = initial.regValue .rdx + BitVec.ofNat 64 offset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have cnt : call.regValue .rdx = 8 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans count
  obtain ⟨t, result, copied, copyAgrees⟩ := P256.Proofs.Program.memcpy_correct callPre cnt (by decide)
  have sp : stackPtr t = stackPtr s := result.rsp.trans (callEffect_stack effect).2
  have full : AgreesExcept (.reg 4 :: copyFrame initial offset) s t := by
    apply (effect.agrees.trans copyAgrees).mono
    simp [copyFrame, P256.Proofs.Program.Copy.copyComponents,
      P256.Proofs.Program.Copy.registerComponents, address, dst]
  have agrees : AgreesExcept (copyFrame initial offset) s t := full.narrow (by
    intro c hc hnot
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact sp
    · exact False.elim (hnot hc))
  have writes : WritesWithin (copyFrame initial offset)
      #v[registerRegion initial .rdx 32, Stack.region initial 128] := by
    intro c hc a ha
    simp only [copyFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim ha
    · exact ⟨Stack.region initial 128, by simp,
        stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) ha⟩
    · exact ⟨registerRegion initial .rdx 32, by simp, output_contains pre bound ha⟩
  have saved : ∀ c ∈ copyFrame initial offset, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
    intro c hc a ha hb
    simp only [copyFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hb
    · obtain ⟨j,hj,rfl⟩ := ha
      obtain ⟨k,hk,eqn⟩ := hb
      have apart : OffsetsApart (-48) 56 (-80) 8 := by unfold OffsetsApart; decide
      exact apart.ne (stackPtr initial) hj hk (by decide) (by simpa only [BitVec.sub_eq_add_neg] using eqn)
    · have stackContains : (Stack.region initial 128).Contains a.toNat := by
        obtain ⟨j,hj,rfl⟩ := ha
        have bounds := stack_bounds pre.stack
        have sn : (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 :=
          stack_sub_toNat pre.stack (by decide)
        apply memoryRegion_contains_add pre.stack.1 (len := 56) _ _ hj
        · rw [sn]; change (stackPtr initial).toNat - 128 ≤ _; omega
        · rw [stack_region_end, sn]; omega
      exact pre.separation (1 : Fin 3) 2 (by decide) _ (output_contains pre bound hb) stackContains
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨t, stage.of_agrees pre (run.trans execution) (readyToStep result.machine result.bindingsSupported)
    agrees writes saved (by simp [copyFrame]), result.rip.trans (callEffect_stack effect).1,
    agrees, ?_⟩
  intro j hj
  have byte := copied j hj
  rw [src, dst] at byte
  refine byte.trans (effect.agrees.memory _ ?_)
  intro c hc cover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact cover
  · rw [address] at cover
    obtain ⟨k,hk,eqn⟩ := cover
    have apart : OffsetsApart (-56) 8 (-80) 8 := by unfold OffsetsApart; decide
    exact apart.ne (stackPtr initial) hj hk (by decide) (by simpa only [BitVec.sub_eq_add_neg] using eqn)
  · exact cover

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
