import P256.Proofs.Program.WrapperArena
import P256.Proofs.EcdhWrapper.Arena
import P256.Proofs.EcdhWrapper.Save

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Initialized [Bindings] (initial s : RamState) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x106808
  rsp : stackPtr s = stackPtr initial - 504
  saved : ∀ entry ∈ savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
      initial.regValue entry.1
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  heapBase : memLoad s.external 0x300000 64 = initial.regValue .r9
  heapCapacity : memLoad s.external 0x300008 64 =
    memLoad initial.external (stackPtr initial+8) 64
  heapUsed : memLoad s.external 0x300010 64 = 0
  agrees : AgreesExcept ((saveFrame initial ++ [.reg 4, .flags, .rip]) ++ arenaComponents) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial)

theorem initialize_correct [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices ecdhDiffieHellman initial [secret, peer] slices) :
    ∃ t, Initialized initial t := by
  obtain ⟨s, hs⟩ := save_correct hb hm hcall
  have pre : ArenaPre s := by
    refine ⟨hs.rip, ?_, ?_⟩
    · have hsp : stackPtr s + 512 = stackPtr initial + 8 := by
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
      (programText_slice (programLoaded_codeIn hs.loaded) 0x67d1 arenaBytes
        (by decide +kernel) (by decide +kernel)) pre
  have agrees : AgreesExcept arenaComponents s t := by
    simpa [arenaEffect, Effect.components, Write.component, Operand.component, arenaComponents] using effect.agrees
  have frame : MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
    apply agrees.memoryWriteFrame
    have lift {off : Nat} (ho : off ∈ ([0,8,16,24,32] : List Nat)) {a : BitVec 64}
        (hc : (Component.mem (0x300000 + BitVec.ofNat 64 off) 8).Covers a) :
        ∃ region ∈ wrapperRegions ecdhDiffieHellman initial, region.Contains a.toNat := by
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
  have fullFrame := memoryWriteFrame_trans (hs.frame hcall.stackAvailable.1) frame
  have saved (entry : Syntax.Reg × Nat) (he : entry ∈ savedRegisters) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
        initial.regValue entry.1 := by
    have bound : entry.2 ≤ ecdhDiffieHellman.minStackBytes := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [arena_preserves_stack_word hcall agrees bound, hs.memory]
    exact saveMemory_saved initial entry he
  have hret := arena_preserves_stack_word hcall agrees (offset := 0) (by decide)
  simp only [BitVec.sub_zero] at hret
  have returnAddress : memLoad t.external (stackPtr initial) 64 =
      (returnBoundary initial).rip := by
    rw [hret, hs.memory]
    change memLoad (saveMemory initial) (stackPtr initial) 64 =
      memLoad initial.external (stackPtr initial) 64
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr initial) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  have heapLength : memLoad s.external (stackPtr s+512) 64 =
      memLoad initial.external (stackPtr initial+8) 64 := by
    have addr : stackPtr s+512 = stackPtr initial+8 := by
      rw [hs.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [addr, hs.memory]
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart _ (stackPtr initial) _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  refine ⟨t, ⟨⟨7 + n, hs.execution.trans run⟩, ready,
    wrapper_frame_loaded hcall hcall.programLoaded fullFrame, effect.rip,
    (agrees.read (n := 64) (r := 4) (by simp [arenaComponents])).trans hs.rsp,
    saved, returnAddress, ?_, ?_, effect.writes.2.2.2.1,
    hs.agrees.trans agrees, fullFrame⟩⟩
  · exact effect.writes.2.1.trans (hs.agrees.read (n := 64) (r := 9)
      (by simp [saveFrame]))
  · exact effect.writes.2.2.1.trans heapLength

end P256.Proofs.EcdhWrapper
