import Sha1.Proofs.Compress.Routine.Interface
import Sha1.Proofs.Common.Reads
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

set_option maxHeartbeats 3200000 in
theorem empty_execution (bindings : Bindings) (c : Context)
    (hv : c.Valid bindings) (hz : c.count = 0) :
    ∃ n t, @Returns bindings (returnBoundary c.initial) n c.initial t ∧
      @ReadyToStep bindings t ∧ Result c t := by
  letI := bindings
  have entryReady : ReadyToStep c.initial := hv.ready
  have entryCode : CodeIn Extracted.programImage c.initial := hv.code
  have hr : MemReadable c.initial c.sp 8 := by
    have hn := hv.call.stackAvailable.2.2.1
    have hb := hv.call.stackAvailable.1
    change Compress.minStackBytes ≤ c.sp.toNat at hn
    change c.sp.toNat - Compress.minStackBytes +
      (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes)) < 2 ^ 32 at hb
    refine ⟨by omega, fun i hi ↦ ?_⟩
    apply Option.isSome_iff_exists.mpr
    apply hv.call.stackAvailable.2.1
    change c.sp.toNat - Compress.minStackBytes ≤ (c.sp + BitVec.ofNat 64 i).toNat ∧
      (c.sp + BitVec.ofNat 64 i).toNat < c.sp.toNat - Compress.minStackBytes +
        (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes))
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega
  have ne1 : (0x1024e0 : BitVec 64) ≠ (returnBoundary c.initial).rip :=
    Machine.outsideCompression_ne hv.outside (by decide +kernel) (by decide +kernel)
  have ne2 : (0x1024e3 : BitVec 64) ≠ (returnBoundary c.initial).rip :=
    Machine.outsideCompression_ne hv.outside (by decide +kernel) (by decide +kernel)
  have ne3 : (0x1036de : BitVec 64) ≠ (returnBoundary c.initial).rip :=
    Machine.outsideCompression_ne hv.outside (by decide +kernel) (by decide +kernel)
  obtain ⟨n0, s1, ha1, ready1, code1, rip1, ag1⟩ :
      ∃ n0 s1, Advances (returnBoundary c.initial) n0 c.initial s1 ∧ ReadyToStep s1 ∧
        CodeIn Extracted.programImage s1 ∧ s1.RIP = 0x1024e0 ∧
        AgreesExcept [.flags, .rip] c.initial s1 := by
    rcases hv.entry with hEntry | hEntry
    · have hc : CodeIn
          (codeRange 0x100000 (0xe9 :: immBytes 32 (0x24db : BitVec 32))) c.initial :=
        Machine.program_text_slice entryCode 0 5 (by decide +kernel)
      obtain ⟨s1, ha, ready, he⟩ :=
        (jmp_rel32_effect_step 0x100000 0x24db (by decide +kernel)).advances
          (boundary := returnBoundary c.initial) entryReady hc hEntry ne1
      have ag : AgreesExcept [.flags, .rip] c.initial s1 :=
        he.agrees.mono (by simp [jmpEffect_components])
      have hm : s1.external = c.initial.external := ag.external (by simp [Component.Covers])
      exact ⟨1, s1, ha, ready, CodeIn.of_external_eq hm entryCode, he.rip, ag⟩
    · exact ⟨0, c.initial, (advances_zero _ _ _).mpr rfl, entryReady,
        entryCode, hEntry, AgreesExcept.refl _ _⟩
  have testCode : CodeIn (codeRange 0x1024e0 [0x48, 0x85, 0xd2]) s1 :=
    Machine.program_text_slice code1 0x24e0 3 (by decide +kernel)
  obtain ⟨s2, ha2, ready2, he2⟩ :=
    (test_r64_r64_effect_step 0x1024e0 0x48 0xd2
      (by decide +kernel) (by decide +kernel)).advances ready1 testCode rip1 ne2
  have ag2 : AgreesExcept [.flags, .rip] c.initial s2 :=
    (ag1.trans he2.agrees).mono (by simp [testR64R64Effect_components])
  have mem2 : s2.external = c.initial.external := ag2.external (by simp [Component.Covers])
  have rdx0 : (Operand.reg 2 : Operand 64).read s1 = 0 := by
    rw [ag1.read (by decide)]
    apply BitVec.eq_of_toNat_eq
    change (c.initial.regValue .rdx).toNat = 0
    have hh := hv.call.blockCountArgumentMatchesBlocks
    change c.blocks.size / 64 = 0 at hz
    omega
  have hzFlag : condHolds 4 (StatusFlags.ofRFLAGS s2.RFLAGS) = true := by
    have hh := he2.flags
    change (testFlags ((Operand.reg 2 : Operand 64).read s1 &&&
      (Operand.reg 2 : Operand 64).read s1)).Allows (StatusFlags.ofRFLAGS s2.RFLAGS) at hh
    have hhZ := hh.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = true
    rw [rdx0] at hhZ
    exact hhZ
  have code2 := CodeIn.of_external_eq mem2 entryCode
  have branchCode : CodeIn (codeRange 0x1024e3
      (0x0f :: jccOpcode32 4 :: immBytes 32 (0x11f5 : BitVec 32))) s2 :=
    Machine.program_text_slice code2 0x24e3 6 (by decide +kernel)
  have eff2 : jccEffect 0x1024e3 6 4 ((0x11f5 : BitVec 32).signExtend 64) s2 =
      (⟨0x1036de, [], none⟩ : Effect) := by
    unfold jccEffect
    rw [hzFlag]
    rfl
  obtain ⟨s3, ha3, ready3, he3⟩ :=
    (jcc_rel32_effect_step 0x1024e3 4 0x11f5).advances
      (boundary := returnBoundary c.initial) ready2 branchCode
      ⟨he2.rip, fun _ ↦ by decide +kernel⟩ (by rw [eff2]; exact ne3)
  have hj := jccEffect_taken hzFlag he3
  have ag3 : AgreesExcept [.flags, .rip] c.initial s3 :=
    (ag2.trans hj.agrees).mono (by simp [jmpEffect_components])
  have mem3 : s3.external = c.initial.external := ag3.external (by simp [Component.Covers])
  have sp3 : stackPtr s3 = c.sp := ag3.read (n := 64) (r := 4) (by decide)
  have top3 : stackTop s3 = stackTop c.initial := by
    simp only [stackTop, Operand.read, sp3, mem3]
    rfl
  have code3 := CodeIn.of_external_eq mem3 entryCode
  have retCode : CodeIn (codeRange 0x1036de [0xc3]) s3 :=
    Machine.program_text_slice code3 0x36de 1 (by decide +kernel)
  have pre3 : RetPre 0x1036de s3 := by
    refine ⟨⟨hj.rip, ?_⟩, ?_⟩
    · rw [sp3]
      exact hr.of_external_eq mem3
    · rw [top3]
      exact hv.returnLow
  obtain ⟨t, hst, readyT, heT⟩ := ret_effect_step 0x1036de s3 ready3 retCode pre3
  have hrip : t.RIP = (returnBoundary c.initial).rip := heT.rip.trans top3
  have hsp : t.GPR[4] = (returnBoundary c.initial).rsp := by
    have hh : stackPtr t = stackPtr s3 + (8 : BitVec 64) := heT.writes
    rw [sp3] at hh
    exact hh
  have hrT : Returns (returnBoundary c.initial) 1 s3 t := Returns.of_step hst hrip hsp
  have hag : AgreesExcept [.reg 4, .flags, .rip] c.initial t :=
    (ag3.trans heT.agrees).mono (by simp [retEffect_components])
  have hmem : t.external = c.initial.external := hag.external (by simp [Component.Covers])
  refine ⟨n0 + (1 + (1 + 1)), t, ha1.returns (ha2.returns (ha3.returns hrT)), readyT, ?_⟩
  refine And.intro ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hag.read (n := 64) (r := 3) (by decide)
    · exact hag.read (n := 64) (r := 5) (by decide)
    · exact hag.read (n := 64) (r := 12) (by decide)
    · exact hag.read (n := 64) (r := 13) (by decide)
    · exact hag.read (n := 64) (r := 14) (by decide)
    · exact hag.read (n := 64) (r := 15) (by decide)
  · refine And.intro (hag.directionFlagClear (by decide) hv.call.directionFlagUnset) ?_
    constructor
    · intro address _
      rw [hmem]
    constructor
    · apply Common.compress_readOutput_of_hasBytes
      have hState : c.state c.count = c.H := by
        rw [hz]
        rfl
      rw [hState]
      rw [hmem]
      exact hv.call.outputInMemory.2.2
    constructor
    · exact hag.rest
    · refine ⟨hag.mono (by simp [compressionChanges]), hrip, hsp, ?_⟩
      have hState : c.state c.count = c.H := by
        rw [hz]
        rfl
      rw [hState, hmem]
      exact hv.call.outputInMemory.2.2


set_option maxHeartbeats 3200000 in
theorem empty_execution_advance (bindings : Bindings) (boundary : ReturnBoundary) (c : Context)
    (hv : c.Valid bindings) (hBoundary : Machine.OutsideCompression boundary.rip)
    (hDifferent : boundary.rip ≠ (returnBoundary c.initial).rip) (hz : c.count = 0) :
    ∃ n t, @Advances bindings boundary n c.initial t ∧
      @ReadyToStep bindings t ∧ Result c t := by
  letI := bindings
  have entryReady : ReadyToStep c.initial := hv.ready
  have entryCode : CodeIn Extracted.programImage c.initial := hv.code
  have hr : MemReadable c.initial c.sp 8 := by
    have hn := hv.call.stackAvailable.2.2.1
    have hb := hv.call.stackAvailable.1
    change Compress.minStackBytes ≤ c.sp.toNat at hn
    change c.sp.toNat - Compress.minStackBytes +
      (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes)) < 2 ^ 32 at hb
    refine ⟨by omega, fun i hi ↦ ?_⟩
    apply Option.isSome_iff_exists.mpr
    apply hv.call.stackAvailable.2.1
    change c.sp.toNat - Compress.minStackBytes ≤ (c.sp + BitVec.ofNat 64 i).toNat ∧
      (c.sp + BitVec.ofNat 64 i).toNat < c.sp.toNat - Compress.minStackBytes +
        (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes))
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega
  have ne1 : (0x1024e0 : BitVec 64) ≠ boundary.rip :=
    Machine.outsideCompression_ne hBoundary (by decide +kernel) (by decide +kernel)
  have ne2 : (0x1024e3 : BitVec 64) ≠ boundary.rip :=
    Machine.outsideCompression_ne hBoundary (by decide +kernel) (by decide +kernel)
  have ne3 : (0x1036de : BitVec 64) ≠ boundary.rip :=
    Machine.outsideCompression_ne hBoundary (by decide +kernel) (by decide +kernel)
  obtain ⟨n0, s1, ha1, ready1, code1, rip1, ag1⟩ :
      ∃ n0 s1, Advances boundary n0 c.initial s1 ∧ ReadyToStep s1 ∧
        CodeIn Extracted.programImage s1 ∧ s1.RIP = 0x1024e0 ∧
        AgreesExcept [.flags, .rip] c.initial s1 := by
    rcases hv.entry with hEntry | hEntry
    · have hc : CodeIn
          (codeRange 0x100000 (0xe9 :: immBytes 32 (0x24db : BitVec 32))) c.initial :=
        Machine.program_text_slice entryCode 0 5 (by decide +kernel)
      obtain ⟨s1, ha, ready, he⟩ :=
        (jmp_rel32_effect_step 0x100000 0x24db (by decide +kernel)).advances
          (boundary := boundary) entryReady hc hEntry ne1
      have ag : AgreesExcept [.flags, .rip] c.initial s1 :=
        he.agrees.mono (by simp [jmpEffect_components])
      have hm : s1.external = c.initial.external := ag.external (by simp [Component.Covers])
      exact ⟨1, s1, ha, ready, CodeIn.of_external_eq hm entryCode, he.rip, ag⟩
    · exact ⟨0, c.initial, (advances_zero _ _ _).mpr rfl, entryReady,
        entryCode, hEntry, AgreesExcept.refl _ _⟩
  have testCode : CodeIn (codeRange 0x1024e0 [0x48, 0x85, 0xd2]) s1 :=
    Machine.program_text_slice code1 0x24e0 3 (by decide +kernel)
  obtain ⟨s2, ha2, ready2, he2⟩ :=
    (test_r64_r64_effect_step 0x1024e0 0x48 0xd2
      (by decide +kernel) (by decide +kernel)).advances ready1 testCode rip1 ne2
  have ag2 : AgreesExcept [.flags, .rip] c.initial s2 :=
    (ag1.trans he2.agrees).mono (by simp [testR64R64Effect_components])
  have mem2 : s2.external = c.initial.external := ag2.external (by simp [Component.Covers])
  have rdx0 : (Operand.reg 2 : Operand 64).read s1 = 0 := by
    rw [ag1.read (by decide)]
    apply BitVec.eq_of_toNat_eq
    change (c.initial.regValue .rdx).toNat = 0
    have hh := hv.call.blockCountArgumentMatchesBlocks
    change c.blocks.size / 64 = 0 at hz
    omega
  have hzFlag : condHolds 4 (StatusFlags.ofRFLAGS s2.RFLAGS) = true := by
    have hh := he2.flags
    change (testFlags ((Operand.reg 2 : Operand 64).read s1 &&&
      (Operand.reg 2 : Operand 64).read s1)).Allows (StatusFlags.ofRFLAGS s2.RFLAGS) at hh
    have hhZ := hh.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = true
    rw [rdx0] at hhZ
    exact hhZ
  have code2 := CodeIn.of_external_eq mem2 entryCode
  have branchCode : CodeIn (codeRange 0x1024e3
      (0x0f :: jccOpcode32 4 :: immBytes 32 (0x11f5 : BitVec 32))) s2 :=
    Machine.program_text_slice code2 0x24e3 6 (by decide +kernel)
  have eff2 : jccEffect 0x1024e3 6 4 ((0x11f5 : BitVec 32).signExtend 64) s2 =
      (⟨0x1036de, [], none⟩ : Effect) := by
    unfold jccEffect
    rw [hzFlag]
    rfl
  obtain ⟨s3, ha3, ready3, he3⟩ :=
    (jcc_rel32_effect_step 0x1024e3 4 0x11f5).advances
      (boundary := boundary) ready2 branchCode
      ⟨he2.rip, fun _ ↦ by decide +kernel⟩ (by rw [eff2]; exact ne3)
  have hj := jccEffect_taken hzFlag he3
  have ag3 : AgreesExcept [.flags, .rip] c.initial s3 :=
    (ag2.trans hj.agrees).mono (by simp [jmpEffect_components])
  have mem3 : s3.external = c.initial.external := ag3.external (by simp [Component.Covers])
  have sp3 : stackPtr s3 = c.sp := ag3.read (n := 64) (r := 4) (by decide)
  have top3 : stackTop s3 = stackTop c.initial := by
    simp only [stackTop, Operand.read, sp3, mem3]
    rfl
  have code3 := CodeIn.of_external_eq mem3 entryCode
  have retCode : CodeIn (codeRange 0x1036de [0xc3]) s3 :=
    Machine.program_text_slice code3 0x36de 1 (by decide +kernel)
  have pre3 : RetPre 0x1036de s3 := by
    refine ⟨⟨hj.rip, ?_⟩, ?_⟩
    · rw [sp3]
      exact hr.of_external_eq mem3
    · rw [top3]
      exact hv.returnLow
  obtain ⟨t, hst, readyT, heT⟩ := ret_effect_step 0x1036de s3 ready3 retCode pre3
  have hrip : t.RIP = (returnBoundary c.initial).rip := heT.rip.trans top3
  have hsp : t.GPR[4] = (returnBoundary c.initial).rsp := by
    have hh : stackPtr t = stackPtr s3 + (8 : BitVec 64) := heT.writes
    rw [sp3] at hh
    exact hh
  have hAdv : Advances boundary 1 s3 t := Advances.of_step hst (Or.inl (by
    rw [hrip]
    exact Ne.symm hDifferent))
  have hag : AgreesExcept [.reg 4, .flags, .rip] c.initial t :=
    (ag3.trans heT.agrees).mono (by simp [retEffect_components])
  have hmem : t.external = c.initial.external := hag.external (by simp [Component.Covers])
  refine ⟨n0 + (1 + (1 + 1)), t, ha1.trans (ha2.trans (ha3.trans hAdv)), readyT, ?_⟩
  refine And.intro ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hag.read (n := 64) (r := 3) (by decide)
    · exact hag.read (n := 64) (r := 5) (by decide)
    · exact hag.read (n := 64) (r := 12) (by decide)
    · exact hag.read (n := 64) (r := 13) (by decide)
    · exact hag.read (n := 64) (r := 14) (by decide)
    · exact hag.read (n := 64) (r := 15) (by decide)
  · refine And.intro (hag.directionFlagClear (by decide) hv.call.directionFlagUnset) ?_
    constructor
    · intro address _
      rw [hmem]
    constructor
    · apply Common.compress_readOutput_of_hasBytes
      have hState : c.state c.count = c.H := by
        rw [hz]
        rfl
      rw [hState]
      rw [hmem]
      exact hv.call.outputInMemory.2.2
    constructor
    · exact hag.rest
    · refine ⟨hag.mono (by simp [compressionChanges]), hrip, hsp, ?_⟩
      have hState : c.state c.count = c.H := by
        rw [hz]
        rfl
      rw [hState, hmem]
      exact hv.call.outputInMemory.2.2

end Sha1.Proofs.Compress.Routine
