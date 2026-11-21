import P256.Proofs.Program.WrapperArena
import P256.Proofs.Verifying.Wrapper.Arena
import P256.Proofs.Verifying.Wrapper.Save

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Initialized [Bindings] (initial s : RamState) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x103057
  rsp : stackPtr s = stackPtr initial - 280
  saved : ∀ entry ∈ savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 = initial.regValue entry.1
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  agrees : AgreesExcept (saveComponents initial ++ arenaComponents) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)

theorem initialize_correct [bindings : Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices) :
    ∃ t, Initialized initial t := by
  obtain ⟨s, hs⟩ := save_correct hb hm hcall
  have pre : ArenaPre s := by
    refine ⟨hs.rip, ?_, ?_⟩
    · have hsp : stackPtr s + 288 = stackPtr initial + 8 := by
        rw [hs.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [hsp]
      exact heap_length_memReadable hcall hs.agrees.grow
    · intro off hoff
      exact call_statics_writable hcall hs.agrees.grow (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        omega)
  obtain ⟨n, t, run, ready, _, effect⟩ :=
    arena_correct (returnBoundary initial) (outer_boundary hcall hm hb) s hs.ready
      (programText_slice (programLoaded_codeIn hs.loaded) 0x3020 arenaBytes
        (by decide +kernel) (by decide +kernel)) pre
  have agrees : AgreesExcept arenaComponents s t := by
    simpa [arenaEffect, Effect.components, Write.component, Operand.component, arenaComponents] using effect.agrees
  have frame : MemoryWriteFrame s t (wrapperRegions verifyingKeyVerify initial) := by
    apply agrees.memoryWriteFrame
    have lift {off : Nat} (ho : off ∈ ([0,8,16,24,32] : List Nat)) {a : BitVec 64}
        (hc : (Component.mem (0x300000 + BitVec.ofNat 64 off) 8).Covers a) :
        ∃ region ∈ wrapperRegions verifyingKeyVerify initial, region.Contains a.toNat := by
      obtain ⟨region, hr, hc⟩ := static_component_within ho hc
      exact ⟨region, by
        have hr' : region = allocatorStateRegion ∨ region = randomSourceRegion := by simpa using hr
        rcases hr' with rfl | rfl <;> simp [wrapperRegions], hc⟩
    intro c hc a hv
    simp only [arenaComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv.elim
    · exact lift (off := 0) (by simp) hv
    · exact lift (off := 8) (by simp) hv
    · exact lift (off := 16) (by simp) hv
    · exact lift (off := 24) (by simp) hv
    · exact lift (off := 32) (by simp) hv
    · exact hv.elim
  have savedFrame := saved_frame hcall.stackAvailable.1 hs
  have fullFrame := memoryWriteFrame_trans savedFrame frame
  have saved : ∀ entry ∈ savedRegisters,
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
        initial.regValue entry.1 := by
    intro entry member
    have bound : entry.2 ≤ verifyingKeyVerify.minStackBytes := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (arena_preserves_stack_word hcall agrees bound).trans
      (hs.memory ▸ savedMemory_saved initial entry member)
  have hret := arena_preserves_stack_word hcall agrees (offset := 0) (by decide)
  simp only [BitVec.sub_zero] at hret
  refine ⟨t, ⟨⟨6 + n, hs.execution.trans run⟩, ready,
    wrapper_frame_loaded hcall hcall.programLoaded fullFrame, effect.rip,
    (agrees.read (n := 64) (r := 4) (by simp [arenaComponents])).trans hs.rsp,
    saved, ?_, hs.agrees.trans agrees, fullFrame⟩⟩
  exact hret.trans (hs.memory ▸ savedMemory_return initial)

end P256.Proofs.Verifying.Wrapper
