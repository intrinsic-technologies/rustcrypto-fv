import P256.Proofs.Verifying.Message.Convert.Z
import P256.Proofs.Projective.Copy
import P256.Proofs.Projective.Constants

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure IdentityCopied [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (x y : Nat) : Prop extends Context initial s boundary message where
  rip : s.RIP = 0x10d9f9
  source : s.regValue .rdx = initial.regValue .rsi
  yPointer : s.regValue .rbx = frameBase initial + 32
  zPointer : s.regValue .r14 = frameBase initial + 64
  identityPointer : s.regValue .r15 = frameBase initial + 128
  x : MontgomeryAt s (frameBase initial + 0) x
  y : MontgomeryAt s (frameBase initial + 32) y
  z : MontgomeryAt s (frameBase initial + 64) 1
  identity : ProjectiveAt s (frameBase initial + 128) Projective.identity

theorem copy_identity [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} (pre : Pre initial boundary message)
    (state : Coordinates initial s boundary message x y) :
    ∃ t, IdentityCopied initial t boundary message x y := by
  obtain ⟨fuel, v, runV, readyV, _, effectV⟩ := identity_setup boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd9df identityBytes
      (by decide) (by decide +kernel)) ⟨state.rip⟩
  have contextV := state.toContext.after_registers runV readyV effectV.agrees
    (by simp [identityEffect, Effect.components, Component.Covers])
    (by simp [identityEffect, Effect.components]) (by simp [identityEffect, Effect.components])
    (by simp [identityEffect, Effect.components]) (by simp [identityEffect, Effect.components])
  have memoryV : v.external = s.external := effectV.agrees.external
    (by simp [identityEffect, Effect.components, Component.Covers])
  have constant : v.regValue .rsi = 0x202490 := effectV.writes.2.2.2
  have destination : v.regValue .rdi = stackPtr initial - 1048 := by
    have hv : v.regValue .rdi = stackPtr s + 128 := effectV.writes.2.2.1
    rw [hv, state.rsp]
    exact frame_address initial 128 (by decide)
  have count : v.regValue .rcx = 12 := effectV.writes.2.1
  have readable : MemReadable v (v.regValue .rsi) 96 := by
    rw [constant]
    exact Projective.Constants.identity_readable contextV.loaded
  have apart : (v.regValue .rsi).toNat+96 ≤ (v.regValue .rdi).toNat ∨
      (v.regValue .rdi).toNat+96 ≤ (v.regValue .rsi).toNat := by
    rw [constant, destination]
    exact Projective.Constants.identity_stack_disjoint pre.toCalleePre (by decide) (by decide)
  have identity : ProjectiveAt v (v.regValue .rsi) Projective.identity := by
    rw [constant]
    exact Projective.Constants.identity_at contextV.loaded
  obtain ⟨t, runT, frameT, ripT, value, agrees⟩ := Projective.Copy.copy_to_stack pre.toCalleePre
    contextV.toFrameState 0xd9f6 (by decide) (by decide +kernel) effectV.rip
    1048 (by decide) (by decide) destination count readable apart identity
  have covers : ∀ (c : Component), c ∈ [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr initial - BitVec.ofNat 64 1048) 96, .rip] → ∀ a, c.Covers a →
      (Component.mem (stackPtr v + BitVec.ofNat 64 128) 96).Covers a := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, contextV.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
  have context := contextV.after_write pre runT
    (readyToStep frameT.machine frameT.bindingsSupported) agrees
    (offset := 128) (len := 96) (by decide) (by decide) covers
    (by simp) (by simp) (by simp) (by simp)
  have keep (offset : Nat) (bound : offset + 32 ≤ 1176) (apart : offset + 32 ≤ 128) :
      ∀ i < 32, t.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [← memoryV]
    exact preserved_bytes pre contextV.toFrameState agrees (offset := 128) (len := 96)
      (readOffset := offset) (readLen := 32) (by decide) bound (.inr (by omega)) covers i hi
  refine ⟨t, context, ripT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 2) (by simp [identityEffect, Effect.components])).trans state.source)
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 3) (by simp [identityEffect, Effect.components])).trans state.yPointer)
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 14) (by simp [identityEffect, Effect.components])).trans state.zPointer)
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans (by
      change v.regValue .r15 = frameBase initial + 128
      have hv : v.regValue .r15 = stackPtr s + 128 := effectV.writes.1
      rw [hv, state.rsp]
      rfl)
  · exact state.x.of_bytes_eq (keep 0 (by decide) (by decide))
  · exact state.y.of_bytes_eq (keep 32 (by decide) (by decide))
  · exact state.z.of_bytes_eq (keep 64 (by decide) (by decide))
  · change ProjectiveAt t (frameBase initial + BitVec.ofNat 64 128) Projective.identity
    rw [frame_address initial 128 (by decide)]
    exact value

end P256.Proofs.Verifying.Message.Convert
