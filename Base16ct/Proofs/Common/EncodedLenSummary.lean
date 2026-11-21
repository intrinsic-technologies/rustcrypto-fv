import Base16ct.Proofs.Common.RoutineSummary
import Base16ct.Proofs.Common.LengthSteps
import Base16ct.Proofs.Common.EncodedLengthStore
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Setup
import Base16ct.Proofs.Common.ReturnSlot

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem encoded_len_add_preserves_store_inputs [bindings : Machine.Bindings]
    {initial s : RamState}
    (hAdd : (addR64R64Effect initial.RIP 6 6 initial).Holds initial s) :
    s.external = initial.external ∧
      s.regValue .rdx = initial.regValue .rdx := by
  refine ⟨hAdd.agrees.external (by simp [Component.Covers]), ?_⟩
  exact hAdd.agrees.read (r := 2) (n := 64) (by simp)

theorem length_store_pre [bindings : Machine.Bindings]
    {initial s : RamState} {byteLength : Nat} {routine : Routine} {lengthWritten : Prop}
    (p : BitVec 64) (offset : Nat)
    (hCall : ValidLengthCall routine initial byteLength lengthWritten)
    (hlengthWritten : lengthWritten)
    (hExternal : s.external = initial.external)
    (hRdx : s.regValue .rdx = initial.regValue .rdx)
    (hRip : s.RIP = p)
    (hoffset : Extracted.textAddress + BitVec.ofNat 64 offset = p)
    (hoffsetBounds : offset + 3 ≤ Extracted.textBytes.size) :
    StorePreAny p 3 (fun q => q.regValue .rdx) 8 s := by
  have hOut := hCall.lengthOutputInMemoryIfLengthWritten hlengthWritten
  have hReadable : MemReadable initial (initial.regValue .rdx) 8 := by
    apply Base16ct.Proofs.Base16ctUpperDecodeCorrect.regionReadable hOut.1 hOut.2
    · exact by simp [lengthOutputRegion, registerRegion]
    · exact by simp [lengthOutputRegion, registerRegion]
  have hReadable' : MemReadable s (s.regValue .rdx) 8 := by
    rw [hRdx]
    exact hReadable.of_external_eq hExternal
  refine ⟨hRip, ?_, ?_, ?_, ?_⟩
  · exact hReadable'.low
  · exact hReadable'.mem
  · by_cases hlo : (s.regValue .rdx).toNat + 8 ≤ 0x1000
    · exact Or.inl hlo
    · apply Or.inr
      by_cases hhi : 0x3000 ≤ (s.regValue .rdx).toNat
      · exact hhi
      · exfalso
        have hAvoid := (hCall.separation.2 (by trivial)).2
        by_cases hstart : 0x1000 ≤ (s.regValue .rdx).toNat
        · have hpage : pageTables.Contains (s.regValue .rdx).toNat := by
            simp [pageTables, MemoryRegion.Contains]
            omega
          have haddr : (lengthOutputRegion initial).Contains (s.regValue .rdx).toNat := by
            simp [lengthOutputRegion, registerRegion, hRdx, MemoryRegion.Contains]
          exact hAvoid _ haddr (.inr hpage)
        · have hpage : pageTables.Contains (0x1000 : BitVec 64).toNat := by
            simp [pageTables, MemoryRegion.Contains]
          have haddr : (lengthOutputRegion initial).Contains (0x1000 : BitVec 64).toNat := by
            change (initial.regValue .rdx).toNat ≤ 0x1000 ∧
              0x1000 < (initial.regValue .rdx).toNat + 8
            rw [← congrArg BitVec.toNat hRdx]
            omega
          exact hAvoid _ haddr (.inr hpage)
  · have hAvoid : ∀ i < 8, ¬ InProgram (s.regValue .rdx + BitVec.ofNat 64 i) := by
      intro i hi hProgram
      apply (hCall.separation.2 (by trivial)).2
        (s.regValue .rdx + BitVec.ofNat 64 i)
      · have hc := region_offset_contains hOut.1 (i := i) hi
        simpa [lengthOutputRegion, registerRegion, hRdx, BitVec.ofNat_add] using hc
      · exact .inl hProgram
    simpa only [hoffset]
      using rangeApart_text (addr := s.regValue .rdx) (len := 8) (offset := offset)
        (count := 3) hAvoid hoffsetBounds

theorem encoded_len_store_pre [bindings : Machine.Bindings]
    {initial s : RamState} {byteLength : Nat}
    (hCall : ValidLengthCall base16ctEncodedLen initial byteLength True)
    (hExternal : s.external = initial.external)
    (hRdx : s.regValue .rdx = initial.regValue .rdx)
    (hRip : s.RIP = 0x100023) :
    StorePreAny s.RIP 3 (fun q => q.regValue .rdx) 8 s := by
  simpa [hRip] using (length_store_pre (p := (0x100023 : BitVec 64)) (offset := 0x23)
    hCall trivial hExternal hRdx hRip (by decide +kernel) (by decide +kernel))

theorem encoded_len_ret_step [bindings : Machine.Bindings] {initial u : RamState}
    (hReady : ReadyToStep u)
    (hCode : CodeIn (codeRange 0x100026 [0xc3]) u)
    (hPre : RetPre 0x100026 u)
    (hTop : stackTop u = (returnBoundary initial).rip)
    (hRsp : stackPtr u + 8#64 = (returnBoundary initial).rsp) :
    ∃ final, Returns (returnBoundary initial) 1 u final ∧ ReadyToStep final ∧
      AgreesExcept [.reg 4, .rip] u final := by
  obtain ⟨final, hstep, hready, he⟩ := ret_effect_step 0x100026 u hReady hCode hPre
  refine ⟨final, ?_, hready, he.agrees⟩
  apply Returns.of_step hstep
  · exact he.rip.trans hTop
  · have hw := he.writes
    change final.GPR[4] = stackPtr u + 8#64 at hw
    exact hw.trans hRsp

end Base16ct.Proofs.Common

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem encoded_len_add_store_trace [bindings : X86.Machine.Bindings]
    {initial : RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctEncodedLen initial byteLength True) :
    ∃ s u, Advances (returnBoundary initial) 1 initial s ∧
      Advances (returnBoundary initial) 1 s u ∧ ReadyToStep u ∧
      AgreesExcept [.reg 6, .flags, .mem (initial.regValue .rdx) 8, .rip] initial u ∧
      u.RIP = 0x100026 ∧
      stackPtr u = stackPtr initial ∧
      (Operand.mem (initial.regValue .rdx) : Operand 64).read u =
        BitVec.ofNat 64 (2 * byteLength) := by
  have hEntry := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.entryReady
    hBindings hMachine hCall.programLoaded
  have hBoundary := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.validReturnAddress_boundary
    hCall.returnAddress
  obtain ⟨s, hAs, hReadyS, hCodeS, hAdd⟩ := Base16ct.Proofs.Common.encoded_len_add_step
    hEntry (by simpa [base16ctEncodedLen, Extracted.encoded_lenAddress] using hCall.entry) hBoundary.2
  have hsRip : s.RIP = 0x100023 := by
    simpa [addR64R64Effect, base16ctEncodedLen, Extracted.encoded_lenAddress, hCall.entry] using hAdd.rip
  have hStorePre := encoded_len_store_pre hCall
    (hAdd.agrees.external (by simp [Component.Covers]))
    (hAdd.agrees.read (r := 2) (n := 64) (by simp)) hsRip
  have hCodeStore : CodeIn (codeRange 0x100023 [0x48, 0x89, 0x32]) s := by
    have h := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.program_text_slice
      hCodeS 0x23 3 (by decide +kernel)
    have hb : Extracted.textBytes.toListFrom 0x23 3 = [0x48, 0x89, 0x32] := by
      decide +kernel
    simpa only [hb, show Extracted.textAddress + BitVec.ofNat 64 0x23 = (0x100023 : BitVec 64) by
      decide +kernel] using h
  have hStorePre' : StorePreAny 0x100023 3 (fun q => q.regValue .rdx) 8 s := by
    simpa [hsRip] using hStorePre
  obtain ⟨u, hSu, hReadyU, hStore⟩ := mov_rsi_store_effect_step (0x100023 : BitVec 64)
    s hReadyS hCodeStore hStorePre'
  have hRdx : s.regValue .rdx = initial.regValue .rdx :=
    hAdd.agrees.read (r := 2) (n := 64) (by simp)
  have hByteLengthLt : byteLength < 2 ^ 64 := by
    have hb := hCall.inputInMemory.2.1
    change (initial.regValue .rdi).toNat + byteLength < 2 ^ 32 at hb
    omega
  have hRsiInitial : initial.regValue .rsi = BitVec.ofNat 64 byteLength := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hByteLengthLt] using
      hCall.lengthArgumentMatchesInput
  have hRsiInitial' : BitVec.setWidth 64 initial.GPR[gprIndex 6] =
      BitVec.ofNat 64 byteLength := by
    change initial.regValue .rsi = _
    exact hRsiInitial
  have hRsi : s.regValue .rsi = BitVec.ofNat 64 (2 * byteLength) := by
    have hw := Write.allHold_iff.mp hAdd.writes
      ⟨(.reg 6 : Operand 64), (Operand.reg 6 : Operand 64).read initial +
        (Operand.reg 6 : Operand 64).read initial⟩
      (by simp [addR64R64Effect])
    change BitVec.setWidth 64 s.GPR[gprIndex 6] =
      BitVec.setWidth 64 initial.GPR[gprIndex 6] + BitVec.setWidth 64 initial.GPR[gprIndex 6] at hw
    rw [hRsiInitial'] at hw
    change BitVec.setWidth 64 s.GPR[gprIndex 6] = _
    rw [show 2 * byteLength = byteLength + byteLength by omega, BitVec.ofNat_add]
    exact hw
  have hValue : (Operand.mem (initial.regValue .rdx) : Operand 64).read u =
      BitVec.ofNat 64 (2 * byteLength) := by
    have hw := hStore.writes
    change (Operand.mem (s.regValue .rdx) : Operand 64).read u =
      (Operand.reg 6 : Operand 64).read s at hw
    rw [hRdx] at hw
    have hw' : (Operand.mem (initial.regValue .rdx) : Operand 64).read u =
        BitVec.setWidth 64 s.GPR[gprIndex 6] := by
      simpa only [Operand.read] using hw
    have hRsi' : BitVec.setWidth 64 s.GPR[gprIndex 6] =
        BitVec.ofNat 64 (2 * byteLength) := by
      change s.regValue .rsi = _
      exact hRsi
    rw [hRsi'] at hw'
    exact hw'
  have hStoreFrame : AgreesExcept [.mem (initial.regValue .rdx) 8, .rip] s u := by
    have hf := hStore.agrees
    simpa only [storeEffect_components, hRdx] using hf
  have hAgree : AgreesExcept [.reg 6, .flags, .mem (initial.regValue .rdx) 8, .rip] initial u :=
    (hAdd.agrees.trans hStoreFrame).mono (by simp)
  have hSu' : Advances (returnBoundary initial) 1 s u := by
    apply Advances.of_step hSu
    left
    rw [hStore.rip]
    exact Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.text_address_ne_return
      hBoundary.2 0x26 (by decide +kernel)
  refine ⟨s, u, hAs, hSu', hReadyU, hAgree, ?_, ?_, hValue⟩
  · exact hStore.rip
  · have hr := hAdd.agrees.trans hStore.agrees
    exact (hr.read (r := 4) (n := 64) (by simp)).trans rfl

end Base16ct.Proofs.Common

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

def encodedLenABI : RoutineABI :=
  { entry := 0x100020
    argumentRegisters := [⟨7, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩]
    resultRegisters := [⟨0, by decide⟩]
    stackBytes := base16ctEncodedLen.minStackBytes
    callbackTarget := none
    codeBytes := 6 }

def encodedLenValues (byteLength : Nat) : RoutineValues :=
  { output := none
    decoded := none
    length := some (2 * byteLength)
    status := none
    sinkCount := none }

theorem encoded_len_routine_summary [bindings : Machine.Bindings]
    {initial : RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctEncodedLen initial byteLength True) :
    ∃ (s u : RamState),
      RoutineSummary encodedLenABI programImage (returnBoundary initial)
        #v[lengthOutputRegion initial, Stack.region initial base16ctEncodedLen.minStackBytes]
        initial u 2
        [.reg 6, .flags, .mem (initial.regValue .rdx) 8, .rip]
        (encodedLenValues byteLength)
        ((Operand.mem (initial.regValue .rdx) : Operand 64).read u =
          BitVec.ofNat 64 (2 * byteLength)) := by
  obtain ⟨s, u, hAs, hSu, hReadyU, hAgree, hRip, hRsp, hValue⟩ :=
    encoded_len_add_store_trace hBindings hMachine hCall
  have hEntry := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.entryReady
    hBindings hMachine hCall.programLoaded
  have hBoundary := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.validReturnAddress_boundary
    hCall.returnAddress
  have hCodeU : CodeIn programImage u := by
    apply CodeIn.of_agreesExcept hAgree
    · intro x hx c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hcov
      · exact hcov
      · obtain ⟨i, hi, heq⟩ := hcov
        have hc := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.region_offset_contains
          (hCall.lengthOutputInMemoryIfLengthWritten (by trivial)).1 hi
        have hc' : (lengthOutputRegion initial).Contains x.1.toNat := by
          rw [heq]
          simpa [lengthOutputRegion, registerRegion] using hc
        exact (hCall.separation.2 (by trivial)).2 x.1 hc' (.inl (⟨x.2, hx⟩))
      · exact hcov
    · exact hEntry.code
  have hInitialReadable := Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack
  have hReadable : MemReadable u (stackPtr initial) 8 :=
    ⟨hInitialReadable.low, fun i hi => hAgree.grow _ (hInitialReadable.mem i hi)⟩
  have hReadableU : MemReadable u (stackPtr u) 8 := by simpa [hRsp] using hReadable
  have hWrites : MemoryWriteFrame initial u
      #v[lengthOutputRegion initial, Stack.region initial base16ctEncodedLen.minStackBytes] := by
    apply hAgree.memoryWriteFrame
    intro c hc x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact False.elim (by change False at hx; exact hx)
    · exact False.elim (by change False at hx; exact hx)
    · obtain ⟨i, hi, heq⟩ := hx
      have hc := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.region_offset_contains
        (hCall.lengthOutputInMemoryIfLengthWritten (by trivial)).1 hi
      have hc' : (lengthOutputRegion initial).Contains x.toNat := by
        rw [heq]
        simpa [lengthOutputRegion, registerRegion] using hc
      exact ⟨lengthOutputRegion initial, by simp, hc'⟩
    · exact False.elim (by change False at hx; exact hx)
  have hCallee : CalleeSavedRegistersUnchanged initial u := by
    intro register hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · change u.GPR[gprIndex (3 : BitVec 5)] = initial.GPR[gprIndex (3 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 3) (by simp) rfl
    · change u.GPR[gprIndex (5 : BitVec 5)] = initial.GPR[gprIndex (5 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 5) (by simp) rfl
    · change u.GPR[gprIndex (12 : BitVec 5)] = initial.GPR[gprIndex (12 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 12) (by simp) rfl
    · change u.GPR[gprIndex (13 : BitVec 5)] = initial.GPR[gprIndex (13 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 13) (by simp) rfl
    · change u.GPR[gprIndex (14 : BitVec 5)] = initial.GPR[gprIndex (14 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 14) (by simp) rfl
    · change u.GPR[gprIndex (15 : BitVec 5)] = initial.GPR[gprIndex (15 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 15) (by simp) rfl
  have hDirection : DirectionFlagUnset u := by
    apply hAgree.directionFlagClear
    · intro hdf
      simp_all
    · exact hCall.directionFlagUnset
  have hTop : stackTop u = (returnBoundary initial).rip := by
    unfold stackTop returnBoundary
    rw [hRsp]
    apply memLoad_congr
    intro i hi
    change (u.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0 =
      (initial.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0
    have hNoStack : ∀ (c : Component), c ∈
        [.reg 6, .flags, .mem (initial.regValue .rdx) 8, .rip] →
        ¬ c.Covers (stackPtr initial + BitVec.ofNat 64 i) := by
      intro c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · simp [Component.Covers] at hcov
      · simp [Component.Covers] at hcov
      · obtain ⟨j, hj, heq⟩ := hcov
        have hLen := region_offset_contains
          (hCall.lengthOutputInMemoryIfLengthWritten (by trivial)).1 hj
        obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds hCall.stack
          (used := 0) (by omega)
        have hStack := Base16ct.Proofs.Base16ctUpperEncodeCorrect.contains_offset_of_subrange
          hCall.stack.1 hs he i hi
        have hStack' : (Stack.region initial base16ctEncodedLen.minStackBytes).Contains
            (stackPtr initial + BitVec.ofNat 64 i).toNat := by
          simpa only [BitVec.sub_zero] using hStack
        have hLen' : (lengthOutputRegion initial).Contains
            (initial.regValue .rdx + BitVec.ofNat 64 j).toNat := by
          simpa [lengthOutputRegion, registerRegion] using hLen
        rw [heq] at hStack'
        exact (hCall.separation.2 (by trivial)).1 _ hLen' hStack'
      · simp [Component.Covers] at hcov
    rw [hAgree.byte hNoStack]
  have hApart : RangeApart encodedLenABI.entry encodedLenABI.codeBytes
      (returnBoundary initial).rip 1 := by
    change RangeApart (0x100020 : BitVec 64) 6 (returnBoundary initial).rip 1
    intro i hi j hj heq
    have hj0 : j = 0 := by omega
    subst j
    rw [BitVec.add_zero] at heq
    apply hBoundary.2
    rw [← heq]
    have hi' : 0x20 + i < Extracted.textBytes.size := by
      have hsize : 0x26 ≤ Extracted.textBytes.size := by decide +kernel
      omega
    have haddr : (0x100020 : BitVec 64) + BitVec.ofNat 64 i =
        Extracted.textAddress + BitVec.ofNat 64 (0x20 + i) := by
      change (BitVec.ofNat 64 1048608) + BitVec.ofNat 64 i =
        (BitVec.ofNat 64 1048576) + BitVec.ofNat 64 (32 + i)
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega
    rw [haddr]
    exact text_address_in_program (0x20 + i) hi'
  refine ⟨s, u, ?_⟩
  refine ⟨hAs.trans hSu, ?_, ?_, hWrites, hAgree, hCallee, hDirection, hValue⟩
  · refine ⟨hEntry.code, hCodeU, hApart, ?_⟩
    simpa [encodedLenABI] using hRip
  · refine ⟨hReadyU, hBoundary, hReadableU, hTop, ?_⟩
    rw [hRsp]
    rfl

end Base16ct.Proofs.Common
