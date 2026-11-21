import P256.Proofs.SignatureFromSlice.Wrapper.Entry.Guards
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.SignatureFromSlice.Wrapper.Interface
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open SavePair Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decoder_entry_correct [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices signatureFromSlice initial [input] slices) :
    ∃ t, DecoderEntry initial t input (returnBoundary initial) := by
  obtain ⟨s, entry⟩ := guards_correct hb hm hcall
  have hs : Stack.Valid initial 656 := hcall.stackAvailable.1
  have hout := outer_boundary hcall hm hb
  obtain ⟨b, hab, rb, ipb, destb, lenb, fb⟩ :=
    call_arguments entry.ready entry.loaded hout entry.rip
  have mb := fb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using entry.loaded
  have spB : stackPtr b = stackPtr initial - 88 :=
    (fb.read (n := 64) (r := 4) (by simp)).trans entry.rsp
  obtain ⟨t, hbt, rt, loadedT, et, memt⟩ := call_rel32_exists hs
    (call_stack_avoids (routine := signatureFromSlice) hcall) hout rb loadedB
    (entry.agrees.trans fb).grow 88 0x227b 0x7840 spB ipb
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x9ac0 (by decide))
  have push : pushAddr b = stackPtr initial - 96 := by
    rw [pushAddr, spB, BitVec.sub_sub]
    rfl
  have ft : AgreesExcept [.reg 4, .mem (stackPtr initial - 96) 8, .rip] b t := by
    simpa only [pushEffect_components, push] using et.agrees
  have spT : stackPtr t = stackPtr initial - 96 := by
    have he : stackPtr t = pushAddr b := et.writes.1
    exact he.trans push
  have retT : (returnBoundary t).rip = 0x102280 := (callEffect_stack et).1
  have dst : t.regValue .rdi = stackPtr initial - 88 :=
    ((ft.read (n := 64) (r := 7) (by simp)).trans destb).trans entry.rsp
  have tail := fb.trans ft
  have total := entry.agrees.trans tail
  have frame : MemoryWriteFrame initial t (wrapperRegions signatureFromSlice initial) := by
    apply memoryWriteFrame_trans entry.frame
    apply tail.memoryWriteFrame
    intro c hc a hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    all_goals try exact hv.elim
    refine ⟨callStack signatureFromSlice initial, by simp [wrapperRegions], ?_⟩
    exact stack_component_within (routine := signatureFromSlice) hs (offset := 96) (len := 8) (by decide) (by decide) hv
  obtain ⟨address, ptr, hn, bound, bytes, _, _, _, _⟩ := preserved_input hcall frame
  have src : t.regValue .rsi = address :=
    ((tail.read (n := 64) (r := 6) (by simp)).trans entry.sourceAddress).trans ptr
  have bytesT : (registerRegion t .rsi input.size).HasBytes t.external input := by
    change (MemoryRegion.mk (t.regValue .rsi).toNat input.size).HasBytes t.external input
    rw [src]
    exact bytes
  have boundT : (registerRegion t .rsi input.size).Bounded := by
    change (MemoryRegion.mk (t.regValue .rsi).toNat input.size).Bounded
    rw [src]
    exact bound
  have apart : (registerRegion t .rsi input.size).Disjoint (Stack.region initial 656) := by
    obtain ⟨original, he, hp, _, _, _, _⟩ := singleton_call_input hcall
    have same : address = original := ptr.symm.trans (word64_memLoad hp)
    have hr : (MemoryRegion.mk address.toNat input.size) ∈ readRegions initial slices := by
      rw [he, same]
      simp [readRegions, Input.region]
    have dis := (hcall.separation.2 (callStack signatureFromSlice initial) (by simp)).1 _ hr
    intro a ha hs
    apply dis a
    · change (MemoryRegion.mk (t.regValue .rsi).toNat input.size).Contains a at ha
      rwa [src] at ha
    · exact stack_contains_callStack hs
  have bt := bindingsSupported_of_ready_agrees hb rt total
  have mt := supportedMachine_of_ready_agrees hm rt total
  have df := total.directionFlagClear
    (by simp [saveComponents, arenaComponents, guardComponents]) hcall.directionFlagUnset
  have pre := CalleePre.of_disjoint_input_and_stack
    (show StackBufferLayout 656 72 560 from
      ⟨96, 88, by decide, by decide, by decide, by decide⟩) hs (call_stack_avoids (routine := signatureFromSlice) hcall)
    bt mt df loadedT et.rip spT boundT (hasBytes_allocated bytesT) apart dst total.grow hout
    (by rw [retT]; exact inProgram_of_textOffset 0x2280 (by decide))
  have wordT {offset : Nat} (ho : offset ≤ 16) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    have last : memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad b.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
      apply memLoad_agrees_apart ft
      intro a len hc
      have he : a = stackPtr initial - 96 ∧ len = 8 := by simpa using hc
      obtain ⟨rfl, rfl⟩ := he
      exact stack_sub_apart hs (a := 96) (b := offset) (na := 8) (nb := 8)
        (by decide) (by omega) (by decide) (by omega) (.inl (by omega))
    rwa [mb] at last
  obtain ⟨fuel, run⟩ := entry.execution
  refine ⟨t, ⟨pre, bytesT, ⟨fuel + 2 + 1, (run.trans hab).trans hbt⟩,
    spT, ?_, dst, ?_, ?_, ?_, ?_, ?_, retT, ?_, frame, total.grow⟩⟩
  · exact ((ft.read (n := 64) (r := 2) (by simp)).trans lenb).trans entry.length
  · exact (tail.read (n := 64) (r := 3) (by simp)).trans entry.output
  · exact (tail.read (n := 64) (r := 14) (by simp)).trans entry.capacity
  · exact (wordT (offset := 16) (by decide)).trans entry.savedRbx
  · exact (wordT (offset := 8) (by decide)).trans entry.savedR14
  · have he := wordT (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at he
    exact he.trans entry.returnAddress
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact total.read (n := 64) (r := 5) (by simp [saveComponents, arenaComponents, guardComponents])
    · exact total.read (n := 64) (r := 12) (by simp [saveComponents, arenaComponents, guardComponents])
    · exact total.read (n := 64) (r := 13) (by simp [saveComponents, arenaComponents, guardComponents])
    · exact total.read (n := 64) (r := 15) (by simp [saveComponents, arenaComponents, guardComponents])

end P256.Proofs.SignatureFromSlice.Wrapper
