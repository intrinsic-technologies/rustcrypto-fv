import Sha1.Proofs.Common.Reads
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse

namespace Sha1.Proofs.Compress.Empty

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Spec Sha1.Spec.Program Standards.NIST

private theorem code_slice {s : RamState} (h : CodeIn Extracted.programImage s)
    (off len : Nat) (hb : off + len ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (0x100000 + BitVec.ofNat 64 off)
      (Extracted.textBytes.toListFrom off len)) s :=
  CodeIn.slice_of_section h
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) off len hb

private theorem jump_code {s : RamState} (h : CodeIn Extracted.programImage s) :
    CodeIn (codeRange 0x100000 (0xE9 :: immBytes 32 (0x24db : BitVec 32))) s := by
  exact code_slice h 0 5 (by decide +kernel)

private theorem test_code {s : RamState} (h : CodeIn Extracted.programImage s) :
    CodeIn (codeRange 0x1024e0 [0x48, 0x85, 0xd2]) s := by
  exact code_slice h 0x24e0 3 (by decide +kernel)

private theorem branch_code {s : RamState} (h : CodeIn Extracted.programImage s) :
    CodeIn (codeRange 0x1024e3 (0x0f :: jccOpcode32 4 :: immBytes 32 (0x11f5 : BitVec 32))) s := by
  exact code_slice h 0x24e3 6 (by decide +kernel)

private theorem return_code {s : RamState} (h : CodeIn Extracted.programImage s) :
    CodeIn (codeRange 0x1036de [0xc3]) s := by
  exact code_slice h 0x36de 1 (by decide +kernel)

private theorem in_program_text (off : Nat) (h : off < Extracted.textBytes.size) :
    InProgram (0x100000 + BitVec.ofNat 64 off) := by
  refine ⟨Extracted.textBytes.getD off, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  apply (mem_codeRange_iff _ _ _).mpr
  refine ⟨⟨off, ?_⟩, ?_⟩
  · simpa only [Bytes.Chunked.toList, Bytes.Chunked.toListFrom,
      List.length_map, List.length_range'] using h
  · simp only [Bytes.Chunked.toList, Bytes.Chunked.toListFrom,
      List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    rfl

private theorem no_memory {s t : RamState} (h : AgreesExcept [.flags, .rip] s t) :
    t.external = s.external :=
  h.external (by simp [Component.Covers])

private theorem stack_readable {s : RamState} (h : Stack.Valid s Compress.minStackBytes) :
    MemReadable s (stackPtr s) 8 := by
  have hn := h.2.2.1
  have hb := h.1
  change Compress.minStackBytes ≤ (stackPtr s).toNat at hn
  change (stackPtr s).toNat - Compress.minStackBytes +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - Compress.minStackBytes)) < 2 ^ 32 at hb
  refine ⟨by omega, fun i hi => ?_⟩
  apply Option.isSome_iff_exists.mpr
  apply h.2.1
  change (stackPtr s).toNat - Compress.minStackBytes ≤
      (stackPtr s + BitVec.ofNat 64 i).toNat ∧
    (stackPtr s + BitVec.ofNat 64 i).toNat <
      (stackPtr s).toNat - Compress.minStackBytes +
        ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - Compress.minStackBytes))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  constructor <;> omega

theorem execution {initial : RamState} {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (bindings : Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial H blocks)
    (hempty : blocks.size = 0) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      @ReadyToStep bindings final ∧ AgreesExcept [.reg 4, .flags, .rip] initial final := by
  letI := bindings
  have entry : EntryReady Extracted.programImage initial :=
    EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
      hBindings.leadingZeroCount hCall.programLoaded (by decide +kernel)
  have hr := stack_readable hCall.stackAvailable
  have hb := nearReturn64Boundary_eq initial entry.ready.dataReady entry.ready.cpu.ss hr
  obtain ⟨boundary, hbound, hlow, hout⟩ := hCall.returnAddress
  rw [hb] at hbound
  obtain rfl := Except.ok.inj hbound
  have outside (p : BitVec 64) (hc : InProgram p) :
      p ≠ (returnBoundary initial).rip := by
    intro he
    exact hout (he ▸ hc)
  have ne1 : (0x1024e0 : BitVec 64) ≠ (returnBoundary initial).rip :=
    outside _ (in_program_text 0x24e0 (by decide +kernel))
  have ne2 : (0x1024e3 : BitVec 64) ≠ (returnBoundary initial).rip :=
    outside _ (in_program_text 0x24e3 (by decide +kernel))
  have ne3 : (0x1036de : BitVec 64) ≠ (returnBoundary initial).rip :=
    outside _ (in_program_text 0x36de (by decide +kernel))
  obtain ⟨s1, ha1, ready1, he1⟩ :=
    (jmp_rel32_effect_step 0x100000 0x24db (by decide +kernel)).advances
      entry.ready (jump_code entry.code) hCall.atEntryPoint ne1
  have ag1 : AgreesExcept [.flags, .rip] initial s1 :=
    he1.agrees.mono (by simp [jmpEffect_components])
  have mem1 := no_memory ag1
  have code1 := CodeIn.of_external_eq mem1 entry.code
  obtain ⟨s2, ha2, ready2, he2⟩ :=
    (test_r64_r64_effect_step 0x1024e0 0x48 0xd2 (by unfold RexWPrefix; decide +kernel) (by decide +kernel)).advances
      ready1 (test_code code1) he1.rip ne2
  have ag2 : AgreesExcept [.flags, .rip] initial s2 :=
    (ag1.trans he2.agrees).mono (by simp [testR64R64Effect_components])
  have mem2 := no_memory ag2
  have rdx0 : (Operand.reg 2 : Operand 64).read s1 = 0 := by
    rw [ag1.read (by decide)]
    have hh := hCall.blockCountArgumentMatchesBlocks
    rw [hempty] at hh
    apply BitVec.eq_of_toNat_eq
    change (initial.regValue .rdx).toNat = 0
    omega
  have hz : condHolds 4 (StatusFlags.ofRFLAGS s2.RFLAGS) = true := by
    have hh := he2.flags
    change (testFlags ((Operand.reg 2 : Operand 64).read s1 &&&
      (Operand.reg 2 : Operand 64).read s1)).Allows (StatusFlags.ofRFLAGS s2.RFLAGS) at hh
    have hz := hh.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = true
    rw [rdx0] at hz
    exact hz
  have code2 := CodeIn.of_external_eq mem2 entry.code
  have eff2 : jccEffect 0x1024e3 6 4 ((0x11f5 : BitVec 32).signExtend 64) s2 =
      (⟨0x1036de, [], none⟩ : Effect) := by
    unfold jccEffect
    rw [hz]
    rfl
  obtain ⟨s3, ha3, ready3, he3⟩ :=
    (jcc_rel32_effect_step 0x1024e3 4 0x11f5).advances
      (boundary := returnBoundary initial) ready2 (branch_code code2)
      ⟨he2.rip, fun _ => by decide +kernel⟩ (by
        rw [eff2]
        exact ne3)
  have hj := jccEffect_taken hz he3
  have ag3 : AgreesExcept [.flags, .rip] initial s3 :=
    (ag2.trans hj.agrees).mono (by simp [jmpEffect_components])
  have mem3 := no_memory ag3
  have sp3 : stackPtr s3 = stackPtr initial :=
    ag3.read (n := 64) (r := 4) (by decide)
  have top3 : stackTop s3 = stackTop initial := by
    simp only [stackTop, Operand.read, sp3, mem3]
  have code3 := CodeIn.of_external_eq mem3 entry.code
  have pre3 : RetPre 0x1036de s3 := by
    refine ⟨⟨hj.rip, ?_⟩, ?_⟩
    · rw [sp3]
      exact hr.of_external_eq mem3
    · rw [top3]
      exact hlow
  obtain ⟨final, hs4, ready4, he4⟩ := ret_effect_step 0x1036de s3 ready3 (return_code code3) pre3
  have hrip : final.RIP = (returnBoundary initial).rip := by
    rw [he4.rip]
    change stackTop s3 = stackTop initial
    exact top3
  have hsp : final.GPR[4] = (returnBoundary initial).rsp := by
    have hh : stackPtr final = stackPtr s3 + (8 : BitVec 64) := he4.writes
    rw [sp3] at hh
    exact hh
  have hr4 : Returns (returnBoundary initial) 1 s3 final :=
    Returns.of_step hs4 hrip hsp
  obtain ⟨fuel, hu⟩ := Returns.unique_of_boundary hb (ha1.returns (ha2.returns (ha3.returns hr4)))
  refine ⟨fuel, final, hu, ready4, ?_⟩
  exact (ag3.trans he4.agrees).mono (by simp [retEffect_components])

end Sha1.Proofs.Compress.Empty

namespace Sha1.Proofs.Compress

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Spec Sha1.Spec.Program Standards.NIST

theorem sha1_compress_writes_state_after_blocks_of_size_eq_zero
    {initial : RamState} {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (bindings : Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial H blocks)
    (hempty : blocks.size = 0) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Compress.outputRegion initial, Stack.region initial Compress.minStackBytes] ∧
      Compress.readOutput initial final =
        .ok (Hasher.stateBytes
          ((SHA2.SHA256.parse (SHA2.bytesToBits blocks)).foldl SHA1.compress H)) := by
  letI := bindings
  obtain ⟨fuel, final, hu, ready, hag⟩ :=
    Empty.execution bindings hBindings hMachine hCall hempty
  have hmem : final.external = initial.external :=
    hag.external (by simp [Component.Covers])
  refine ⟨fuel, final, hu, ready.supported (SupportedSSE.of_agreesExcept hag hMachine.sse),
    ⟨ready.smrr, ready.memoryType, hBindings.stringStride, ready.features.lzcnt⟩, ?_,
    hag.directionFlagClear (by decide) hCall.directionFlagUnset, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hag.read (n := 64) (r := 3) (by decide)
    · exact hag.read (n := 64) (r := 5) (by decide)
    · exact hag.read (n := 64) (r := 12) (by decide)
    · exact hag.read (n := 64) (r := 13) (by decide)
    · exact hag.read (n := 64) (r := 14) (by decide)
    · exact hag.read (n := 64) (r := 15) (by decide)
  · intro address _
    rw [hmem]
  · have hb : blocks.data = #[] := Array.eq_empty_of_size_eq_zero hempty
    have hbits : SHA2.bytesToBits blocks = #[] := by
      rw [SHA2.bytesToBits, hb]
      rfl
    have hparse : SHA2.SHA256.parse (SHA2.bytesToBits blocks) = #[] := by
      rw [hbits]
      rfl
    rw [hparse, Array.foldl_empty]
    apply Sha1.Proofs.Common.compress_readOutput_of_hasBytes
    rw [hmem]
    exact hCall.outputInMemory.2.2

end Sha1.Proofs.Compress
