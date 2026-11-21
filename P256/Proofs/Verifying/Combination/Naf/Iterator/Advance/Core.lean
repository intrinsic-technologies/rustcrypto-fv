import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

set_option maxHeartbeats 2400000 in
theorem core [Bindings] {s : RamState} {boundary : ReturnBoundary} {source : BitVec 64} {n k q : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1181b4)
    (state : StateAt s (s.regValue .rdi) source n k)
    (write : Writable s (s.regValue .rdi) 40)
    (outBounded : (registerRegion s .rdi 40).Bounded)
    (avoid : ∀ i < 40, ¬ InProgram (s.regValue .rdi + BitVec.ofNat 64 i))
    (sourceBounded : (⟨source.toNat,32⟩ : MemoryRegion).Bounded)
    (sourceRead : MemReadable s source 32)
    (apart : (⟨source.toNat,32⟩ : MemoryRegion).Disjoint (registerRegion s .rdi 40))
    (input : Nat256At s source n)
    (requested : s.regValue .rsi = BitVec.ofNat 64 q) (step : q=k ∨ q=k+1) (bound : q<4)
    (outer : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (t.RIP = 0x118234 ∨ t.RIP = 0x118246 ∨ t.RIP = 0x118267) ∧
      StateAt t (s.regValue .rdi) source n q ∧
      t.regValue .rax = word n q ∧ t.regValue .rdx = word n (q+1) ∧
      AgreesExcept (coreComponents (s.regValue .rdi)) s t := by
  obtain ⟨fuelG, g, runG, readyG, loadedG, ripG, gx, agG⟩ := guard ready loaded rip
    (readable_subrange write.toMemReadable 16 8 (by decide)) state.index requested step bound outer
  have mg := agG.external (by simp [Component.Covers])
  have gp : g.regValue .rdi = s.regValue .rdi := agG.read (n := 64) (r := 7) (by simp)
  have wg : Writable g (g.regValue .rdi) 40 := by
    rw [gp]; exact writable_grow write agG.grow
  by_cases same : q=k
  · obtain ⟨t, runT, readyT, loadedT, ripT, tx, td, agT⟩ := cached readyG loadedG
      (by simpa only [same, ↓reduceIte] using ripG) wg.toMemReadable outer
    have mt := agT.external (by simp [Component.Covers])
    refine ⟨fuelG+2, t, runG.trans runT, readyT, loadedT, .inl ripT,
      ?_, ?_, ?_, (agG.trans agT).mono (by simp [coreComponents])⟩
    · rw [same]; exact state_of_external state (mt.trans mg)
    · rw [gp, mg, state.low, ← same] at tx; exact tx
    · rw [gp, mg, state.high, ← same] at td; exact td
  · have successor : q=k+1 := step.resolve_left same
    subst q
    obtain ⟨h, runH, readyH, loadedH, effectH⟩ := shift readyG loadedG
      (by simpa only [same, ↓reduceIte] using ripG) wg (by rw [gp]; exact avoid) outer
    have agH : AgreesExcept (coreComponents (s.regValue .rdi)) s h := by
      apply (agG.trans effectH.agrees).mono
      simp [shiftEffect, Effect.components, coreComponents, gp]
    have hp : h.regValue .rdi = s.regValue .rdi := agH.read (n := 64) (r := 7) (by simp [coreComponents])
    have highG : memLoad g.external (g.regValue .rdi+32) 64 = word n (k+1) := by
      rw [gp, mg]; exact state.high
    have remainG : memLoad g.external (g.regValue .rdi+8) 64 = BitVec.ofNat 64 (8*(4-(k+2))) := by
      rw [gp, mg]; exact state.remaining
    have stores := effectH.writes
    change memLoad h.external (g.regValue .rdi+16) 64 = g.regValue .rax ∧
      memLoad h.external (g.regValue .rdi+24) 64 = memLoad g.external (g.regValue .rdi+32) 64 ∧
      h.regValue .rcx = memLoad g.external (g.regValue .rdi+8) 64 ∧
      h.regValue .rax = memLoad g.external (g.regValue .rdi+32) 64 at stores
    have hc : h.regValue .rcx = BitVec.ofNat 64 (8*(4-(k+2))) := stores.2.2.1.trans remainG
    obtain ⟨fuelV, v, runV, readyV, loadedV, ripV, frameV⟩ := select readyH loadedH effectH.rip hc
      (by have hk : k=0 ∨ k=1 ∨ k=2 := by omega
          rcases hk with rfl | rfl | rfl <;> decide) outer
    have mv := frameV.external (by simp [Component.Covers])
    have agV : AgreesExcept (coreComponents (s.regValue .rdi)) s v :=
      (agH.trans frameV).mono (by simp [coreComponents])
    have vp : v.regValue .rdi = s.regValue .rdi := agV.read (n := 64) (r := 7) (by simp [coreComponents])
    have vc : v.regValue .rcx = BitVec.ofNat 64 (8*(4-(k+2))) :=
      (frameV.read (n := 64) (r := 1) (by simp)).trans hc
    have vx : v.regValue .rax = word n (k+1) :=
      (frameV.read (n := 64) (r := 0) (by simp)).trans (stores.2.2.2.trans highG)
    have indexV : memLoad v.external (v.regValue .rdi+16) 64 = BitVec.ofNat 64 (k+1) := by
      rw [vp, mv, ← gp]; exact stores.1.trans gx
    have lowV : memLoad v.external (v.regValue .rdi+24) 64 = word n (k+1) := by
      rw [vp, mv, ← gp]; exact stores.2.1.trans highG
    have pointerV : memLoad v.external (v.regValue .rdi) 64 = source + BitVec.ofNat 64 (8*min (k+2) 4) := by
      rw [vp, mv, ← gp, ← BitVec.add_zero (g.regValue .rdi)]
      rw [shift_read effectH (0#64) (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)]
      rw [BitVec.add_zero, gp, mg]; exact state.pointer
    have remainingV : memLoad v.external (v.regValue .rdi+8) 64 = BitVec.ofNat 64 (8*(4-(k+2))) := by
      rw [vp, mv, ← gp]
      rw [shift_read effectH 8 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)]
      exact remainG
    have wv : Writable v (v.regValue .rdi) 40 := by rw [vp]; exact writable_grow write agV.grow
    by_cases exhausted : 8*(4-(k+2))=0
    · have hk : k=2 := by omega
      obtain ⟨t, runT, readyT, loadedT, effectT⟩ := empty readyV loadedV
        (by simpa only [exhausted, ↓reduceIte] using ripV) (wv.add 32 (by decide))
        (by intro i hi; rw [vp, BitVec.add_assoc]
            have h := avoid (32+i) (by omega)
            simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using h) outer
      have result := effectT.writes
      change memLoad t.external (v.regValue .rdi+32) 64 = 0 ∧ t.regValue .rdx = 0 at result
      have agT : AgreesExcept (coreComponents (s.regValue .rdi)) s t := by
        apply (agV.trans effectT.agrees).mono
        simp [emptyEffect, Effect.components, coreComponents, vp]
      refine ⟨fuelG+4+fuelV+2, t, ((runG.trans runH).trans runV).trans runT,
        readyT, loadedT, .inr (.inl effectT.rip), ?_, ?_, ?_, agT⟩
      · rw [← vp]
        constructor
        · rw [← BitVec.add_zero (v.regValue .rdi), empty_read effectT (0#64) (by unfold OffsetsApart; decide +kernel),
            BitVec.add_zero, pointerV, hk]
          rfl
        · rw [empty_read effectT 8 (by unfold OffsetsApart; decide +kernel), remainingV, hk]
        · rw [empty_read effectT 16 (by unfold OffsetsApart; decide +kernel)]
          exact indexV
        · rw [empty_read effectT 24 (by unfold OffsetsApart; decide +kernel)]
          exact lowV
        · rw [result.1, hk]
          exact (word_four input.1).symm
      · exact (effectT.agrees.read (n := 64) (r := 0)
          (by simp [emptyEffect, Effect.components])).trans vx
      · rw [result.2, hk]; exact (word_four input.1).symm
    · have hk : k=0 ∨ k=1 := by omega
      have small : k+2 < 4 := by omega
      have pointerV' : memLoad v.external (v.regValue .rdi) 64 = source + BitVec.ofNat 64 (8*(k+2)) := by
        rw [pointerV, Nat.min_eq_left (by omega)]
      have readV : MemReadable v (memLoad v.external (v.regValue .rdi) 64) 8 := by
        rw [pointerV']
        exact readable_of_grow
          (readable_subrange sourceRead (8*(k+2)) 8 (by omega)) agV.grow
      have inputV := source_preserved input sourceBounded apart (core_frame outBounded agV)
      have nextWord : memLoad v.external (memLoad v.external (v.regValue .rdi) 64) 64 = word n (k+2) := by
        rw [pointerV']; exact inputV.memLoad_limb (k+2) small
      obtain ⟨t, runT, readyT, loadedT, effectT⟩ := full readyV loadedV
        (by simpa only [exhausted, ↓reduceIte] using ripV) wv readV (by rw [vp]; exact avoid) outer
      have result := effectT.writes
      change memLoad t.external (v.regValue .rdi+32) 64 = memLoad v.external (memLoad v.external (v.regValue .rdi) 64) 64 ∧
        memLoad t.external (v.regValue .rdi) 64 = memLoad v.external (v.regValue .rdi) 64 + 8 ∧
        memLoad t.external (v.regValue .rdi+8) 64 = v.regValue .rcx-8 ∧
        t.regValue .rsi = memLoad v.external (v.regValue .rdi) 64 + 8 ∧
        t.regValue .rdx = memLoad v.external (memLoad v.external (v.regValue .rdi) 64) 64 ∧
        t.regValue .rcx = v.regValue .rcx-8 at result
      have agT : AgreesExcept (coreComponents (s.regValue .rdi)) s t := by
        apply (agV.trans effectT.agrees).mono
        simp [fullEffect, Effect.components, coreComponents, vp]
      refine ⟨fuelG+4+fuelV+7, t, ((runG.trans runH).trans runV).trans runT,
        readyT, loadedT, .inr (.inr effectT.rip), ?_, ?_, ?_, agT⟩
      · rw [← vp]
        constructor
        · rw [result.2.1, pointerV']
          rcases hk with rfl | rfl <;> simp only [BitVec.add_assoc] <;> rfl
        · rw [result.2.2.1, vc]
          rcases hk with rfl | rfl <;> decide +kernel
        · rw [full_read effectT 16 (by unfold OffsetsApart; decide +kernel)
            (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)]
          exact indexV
        · rw [full_read effectT 24 (by unfold OffsetsApart; decide +kernel)
            (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)]
          exact lowV
        · exact result.1.trans nextWord
      · exact (effectT.agrees.read (n := 64) (r := 0)
          (by simp [fullEffect, Effect.components])).trans vx
      · exact result.2.2.2.2.1.trans nextWord

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
