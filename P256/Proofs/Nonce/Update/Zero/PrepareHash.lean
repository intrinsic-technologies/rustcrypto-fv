import P256.Proofs.Nonce.Update.Zero.State
import P256.Proofs.Nonce.Update.Zero.HashSetup
import P256.Proofs.Nonce.Update.Zero.Memory
import P256.Proofs.Program.ScalarFrame.Copy32

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {original state : State} {input : ByteArray}

theorem prepare_hash (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Copied initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧ HashReady initial t state input := by
  have hp : HashSetup.Pre s := by
    refine ⟨current.rip, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact stack_writable8 pre current.toFrameState (by decide) (by decide)
    · intro i hi pc len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact ScalarFrame.stack_code pre.callee current.toFrameState (by decide) (by decide) bound
  obtain ⟨fuel, t, run, ready, _, effect⟩ := HashSetup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported)
    (programText_slice (programLoaded_codeIn current.loaded) 0xa3b7 HashSetup.bytes
      (by decide +kernel) (by decide +kernel)) hp
  have agrees : AgreesExcept [.reg 6, .reg 7, .mem (scratch initial + 256) 8,
      .mem (scratch initial + 264) 8, .mem (scratch initial + 272) 8,
      .mem (scratch initial + 280) 8, .rip] s t := by
    have rsp : (Operand.reg 4 : Operand 64).read s = scratch initial := current.rsp
    simpa only [HashSetup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      rsp] using effect.agrees
  have writes : ∀ (c : Component), c ∈ [.reg 6, .reg 7, .mem (scratch initial + 256) 8,
      .mem (scratch initial + 264) 8, .mem (scratch initial + 272) 8,
      .mem (scratch initial + 280) 8, .rip] → ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · apply work_contains_scratch pre (offset := 256) (len := 8) (by decide)
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ha
    · exact work_contains_scratch pre (offset := 264) (by decide) ha
    · exact work_contains_scratch pre (offset := 272) (by decide) ha
    · exact work_contains_scratch pre (offset := 280) (by decide) ha
  have frame := current.toFrameState.after_effect pre.callee (by decide) ready agrees
    (fun c hc a ha => ⟨ScalarFrame.workRegion initial 1856, by simp, writes c hc a ha⟩)
    (by simp)
  have drbg : DrbgAt t (initial.regValue .rdi) state := by
    apply current.drbg.copy
    intro i hi
    apply agrees.byte
    intro c hc ha
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (work_substack pre (writes c hc _ ha))
  have keep {off len : Nat} (apart : off + len ≤ 256 ∨ 288 ≤ off) (bound : off + len ≤ 680) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agrees.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨j, hj, he⟩ := ha
    · exact RangeApart.offsets (scratch initial) (a := 256) (b := off)
        (by decide) (by omega) (by omega) j hj i hi
        (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm)
    · exact RangeApart.offsets (scratch initial) (a := 264) (b := off)
        (by decide) (by omega) (by omega) j hj i hi he.symm
    · exact RangeApart.offsets (scratch initial) (a := 272) (b := off)
        (by decide) (by omega) (by omega) j hj i hi he.symm
    · exact RangeApart.offsets (scratch initial) (a := 280) (b := off)
        (by decide) (by omega) (by omega) j hj i hi he.symm
  have context := current.toContext.of_copied frame drbg
    ((agrees.read (n := 64) (r := 5) (by simp)).trans current.descriptors)
    (by
      intro offset member i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact keep (by decide) (by decide) i hi)
  have out := effect.writes
  change t.regValue .rsi = stackPtr s + 256 ∧ t.regValue .rdi = s.regValue .rbx ∧ _ at out
  exact ⟨fuel, t, run, context, effect.rip,
    out.2.1.trans current.hashPointer, out.1.trans (congrArg (· + 256) current.rsp),
    current.hmac.copy (keep (by decide) (by decide))⟩

end P256.Proofs.Nonce.Update.Zero
