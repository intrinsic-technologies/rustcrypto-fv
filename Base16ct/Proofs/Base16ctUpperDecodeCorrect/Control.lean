import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Control.Entry
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Control.Epilogue
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Loop
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopStatefulLoaded
import Base16ct.Proofs.Common.Output

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
variable {alphabet : RFC4648.Alphabet} {lengthWritten : Prop}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode_early_return [Bindings]
    {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (he : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 240#64)
    (hf : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial s) :
    ∃ t, Returns (returnBoundary initial) 1 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 0, .reg 4, .reg 9, .flags, .rip] initial t ∧
      MemoryWriteFrame initial t
        #v[Stack.region initial (decodeRoutine alphabet).minStackBytes] ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      AddrMode.reg64 0 t = AddrMode.reg64 0 s := by
  have hm : s.external = initial.external := hf.external (by simp [Component.Covers])
  have hsp : stackPtr s = stackPtr initial := hf.read (r := 4) (n := 64) (by simp)
  have htop : stackTop s = stackTop initial := by simp [stackTop, Operand.read, hm, hsp]
  have hb : returnBoundary s = returnBoundary initial := by
    change ({rip := stackTop s, rsp := stackPtr s + 8#64} : ReturnBoundary) =
      {rip := stackTop initial, rsp := stackPtr initial + 8#64}
    rw [hsp, htop]
  have hread : MemReadable s (stackPtr s) 8 := by
    rw [hsp]
    exact (returnSlotReadable hv).of_external_eq hm
  have hvb := returnBoundaryValid hv
  obtain ⟨t, hat, hrt, hft⟩ := decode_return_suffix he hp (Or.inl rfl) hread
    (by rw [htop]; exact hvb.1)
  rw [hb] at hat
  have hfull : AgreesExcept [.reg 0, .reg 4, .reg 9, .flags, .rip] initial t :=
    (hf.trans hft).mono (by simp_all)
  have hframe : MemoryWriteFrame initial t
      #v[Stack.region initial (decodeRoutine alphabet).minStackBytes] := by
    intro a _
    exact hfull.byte (by simp [Component.Covers])
  have hcallee : CalleeSavedRegistersUnchanged initial t := by
    intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfull.read (r := 3) (n := 64) (by simp)
    · exact hfull.read (r := 5) (n := 64) (by simp)
    · exact hfull.read (r := 12) (n := 64) (by simp)
    · exact hfull.read (r := 13) (n := 64) (by simp)
    · exact hfull.read (r := 14) (n := 64) (by simp)
    · exact hfull.read (r := 15) (n := 64) (by simp)
  exact ⟨t, hat, hrt, hfull, hframe, hcallee,
    hfull.directionFlagClear (by simp) hv.directionFlagUnset, hft.read (by simp)⟩


theorem decode_empty_return [Bindings]
    {initial s : RamState} {capacity : Nat}
    (hv : ValidCall (decodeRoutine alphabet) initial [] capacity lengthWritten)
    (hsuccess : lengthWritten)
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 241#64)
    (hf : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial s)
    (h9 : AddrMode.reg64 9 s = 0#64) :
    ∃ t, Returns (returnBoundary initial) 5 s t ∧ ReadyToStep t ∧
      AgreesExcept [.mem (initial.regValue .rdx) 8, .reg 0, .reg 4, .reg 9,
        .flags, .rip] initial t ∧
      AddrMode.reg64 0 t = 0#64 ∧
      memLoad t.external (initial.regValue .rdx) 64 = 0#64 := by
  have hb := returnBoundaryValid hv
  have hcx : AddrMode.reg64 1 s = initial.regValue .rcx := hf.read (by simp)
  have hnon : AddrMode.reg64 1 s ≠ 0#64 := by
    rw [hcx]
    intro hz
    have hn := hv.outputInMemory.1
    change (initial.regValue .rcx).toNat ≠ 0 at hn
    exact hn (congrArg BitVec.toNat hz)
  obtain ⟨u, hau, heu, hpu, hfu⟩ := decode_empty_prepare he hp hnon hb.2
  have hiu : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial u :=
    (hf.trans hfu).mono (by simp)
  have hm : u.external = initial.external := hiu.external (by simp [Component.Covers])
  have hsp : stackPtr u = stackPtr initial := hiu.read (r := 4) (n := 64) (by simp)
  have hdx : AddrMode.reg64 2 u = initial.regValue .rdx := hiu.read (by simp)
  have htop : stackTop u = stackTop initial := by simp [stackTop, Operand.read, hsp, hm]
  have hboundary : returnBoundary u = returnBoundary initial := by
    change ({rip := stackTop u, rsp := stackPtr u + 8#64} : ReturnBoundary) =
      {rip := stackTop initial, rsp := stackPtr initial + 8#64}
    rw [htop, hsp]
  obtain ⟨hw, havoid, hapart, _⟩ := decode_length_output_ready hv hsuccess hiu (by simp)
  have haddr : storeAddrAt u.RIP (.base 2 .none) 3 u = initial.regValue .rdx := by
    simpa [storeAddrAt, AddrMode.addr, Disp.value] using hdx
  have hpre : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre u.RIP 3
      (storeAddrAt u.RIP (.base 2 .none) 3) 8 u := by
    refine ⟨rfl, ?_, ?_⟩
    · rw [haddr]; exact hw
    · rw [haddr]
      intro i hi j hj heq
      apply havoid i hi
      rw [heq, hpu]
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj' with rfl | rfl | rfl
      · exact ⟨0x4c, by cases alphabet <;> decide +kernel⟩
      · exact ⟨0x89, by cases alphabet <;> decide +kernel⟩
      · exact ⟨0x0a, by cases alphabet <;> decide +kernel⟩
  have ha : (movM64R64Effect u.RIP 9 (.base 2 .none) u).Avoids programImage := by
    intro x hx c hc hcover
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := hcover
      change x.1 = storeAddrAt u.RIP (.base 2 .none) 3 u + BitVec.ofNat 64 i at heq
      apply havoid i hi
      rw [← haddr, ← heq]
      exact ⟨x.2, hx⟩
    · exact hcover
  have hread : MemReadable u (stackPtr u) 8 := by
    rw [hsp]
    exact (returnSlotReadable hv).of_external_eq hm
  obtain ⟨t, hat, hrt, hft, hzero, hlen⟩ := decode_success_suffix heu hpu hpre ha hread
    (by rw [hdx, hsp]; exact hapart) (by rw [htop]; exact hb.1)
    (by rw [htop]; exact hb.2)
  rw [hboundary] at hat
  refine ⟨t, hau.returns hat, hrt, ?_, hzero, ?_⟩
  · rw [hdx] at hft
    exact (hiu.trans hft).mono (by simp)
  · have h9u : AddrMode.reg64 9 u = AddrMode.reg64 9 s := hfu.read (r := 9) (n := 64) (by simp)
    rw [hdx, h9u, h9] at hlen
    exact hlen


theorem decode_correct (alphabet : RFC4648.Alphabet) :
    CallComputes (decodeRoutine alphabet) (pairDecodeResult [alphabet]) := by
  intro bindings initial input capacity hBindings hs hv
  have he := entryReady hBindings.smrr hBindings.memoryType hs hBindings.leadingZeroCount hv
  have hb := returnBoundaryValid hv
  by_cases hi : input.length % 2 ≠ 0 ∨ capacity < input.length / 2
  · obtain ⟨fuel, s, has, hes, hps, hfs, hax⟩ :=
      decode_entry_invalid (boundary := returnBoundary initial) hv he hi hb.2
    obtain ⟨t, hat, hrt, hft, hframe, hcallee, hdf, hax'⟩ :=
      decode_early_return hv hes hps hfs
    obtain ⟨least, hleast⟩ := returnedUnique hv he.ready (has.returns hat)
    refine ⟨least, t, hleast, supportedAfter hs hrt hft,
      ⟨hrt.smrr, hrt.memoryType, hBindings.stringStride, hrt.features.lzcnt⟩,
      hcallee, hdf, ?_⟩
    rw [pairDecodeResult, ite_eq_left hi]
    refine ⟨?_, hframe⟩
    have h : AddrMode.reg64 0 t = 1#64 := hax'.trans hax
    simpa [FailureStatus, invalidLengthStatus, AddrMode.reg64, State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using
      congrArg (fun x : BitVec 64 => x.setWidth 32) h
  · have heven : input.length % 2 = 0 := by omega
    have hcapacity : input.length / 2 ≤ capacity := by omega
    by_cases hn : input = []
    · subst input
      have hresult : pairDecodeResult [alphabet] [] capacity = .ok [] := by
        simp [pairDecodeResult, RFC4648.decode]
      have hsuccess : ∃ output, pairDecodeResult [alphabet] [] capacity = .ok output :=
        ⟨[], hresult⟩
      obtain ⟨s, has, hes, hps, hfs, h9⟩ :=
        decode_entry_empty (boundary := returnBoundary initial) hv he hb.2
      obtain ⟨t, hat, hrt, hft, hax, hlen⟩ := decode_empty_return hv hsuccess hes hps hfs h9
      obtain ⟨least, hleast⟩ := returnedUnique hv he.ready (has.returns hat)
      have hcallee : CalleeSavedRegistersUnchanged initial t := by
        intro reg hreg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
        rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hft.read (r := 3) (n := 64) (by simp)
        · exact hft.read (r := 5) (n := 64) (by simp)
        · exact hft.read (r := 12) (n := 64) (by simp)
        · exact hft.read (r := 13) (n := 64) (by simp)
        · exact hft.read (r := 14) (n := 64) (by simp)
        · exact hft.read (r := 15) (n := 64) (by simp)
      refine ⟨least, t, hleast, supportedAfter hs hrt hft,
        ⟨hrt.smrr, hrt.memoryType, hBindings.stringStride, hrt.features.lzcnt⟩,
        hcallee, hft.directionFlagClear (by simp) hv.directionFlagUnset, ?_⟩
      rw [hresult]
      refine ⟨?_, ?_, rfl, ?_⟩
      · simpa [SuccessfulStatus, AddrMode.reg64, State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using
          congrArg (fun x : BitVec 64 => x.setWidth 32) hax
      · apply hft.memoryWriteFrame
        intro c hc address hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨j, hj, heq⟩ := hcover
          refine ⟨lengthOutputRegion initial, by simp, ?_⟩
          rw [heq]
          simpa [lengthOutputRegion, registerRegion, BitVec.ofNat_add] using
            (region_contains_offset (hv.lengthOutputInMemoryIfLengthWritten hsuccess).1 hj)
        all_goals exact False.elim hcover
      · have hw := (decode_length_output_ready hv hsuccess hft (by simp)).1
        exact Base16ct.Proofs.readLengthOutput_of_operand_read hw.readable hlen
    · obtain ⟨s, has, hes, hloop⟩ :=
        decode_entry_nonempty (boundary := returnBoundary initial) hv he heven hcapacity hn hb.2
      obtain ⟨u, hau, heu, hdone⟩ := decode_machine_loop
        (show DecodeLoopStep (decodeRoutine alphabet) [alphabet] 228 46 from
          decode_loop_step_values) (by simp [decodeRoutine]) hv hes hloop heven hcapacity hb.2
        (by simp) (by intro c hc; simp [decodeCallEffects, hc])
      obtain ⟨fuel, t, hat, hrt, hcallee, hdf, hft, hresult⟩ :=
        decode_completed_loop hv heu hdone heven hcapacity
      obtain ⟨least, hleast⟩ := returnedUnique hv he.ready (has.returns (hau.returns hat))
      exact ⟨least, t, hleast, supportedAfter hs hrt hft,
        ⟨hrt.smrr, hrt.memoryType, hBindings.stringStride, hrt.features.lzcnt⟩,
        hcallee, hdf, hresult⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
