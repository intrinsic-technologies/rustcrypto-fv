import Sha3.Proofs.Finalize.Finish
import Sha3.Proofs.Finalize.Output.Full
import Sha3.Proofs.Memcpy
import Sha3.Proofs.LaneMemory
import Sha3.Proofs.Image
import Sha3.Proofs.X86.Instructions.Branch.IndirectJump

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem SavedFrame.after_memcpy_frame {boundary : ReturnBoundary} {v : Variant}
    {reset keccak fullState : Bool} {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre boundary v reset state initial keccak fullState)
    (h : SavedFrame v initial s fullState)
    (ha : AgreesExcept (Memcpy.clobbers (initial.regValue .rsi)
      (v.digestBytes fullState)) s t) : SavedFrame v initial t fullState := by
  have hsaved : CalleeSavedRegistersUnchanged s t :=
    calleeSavedRegistersUnchanged_of_agreesExcept ha (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [Memcpy.clobbers])
  have hslot (k : Nat) (hk : k ≤ 16) :
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read t =
        (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read s := by
    apply read_of_agrees ha
    intro i hi c hc hcover
    simp only [Memcpy.clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try exact hcover
    obtain ⟨j, hj, he⟩ := hcover
    apply hp.outputStack j hj (296 - k + i) (by omega)
    rw [frame_offset initial (by omega : k ≤ 296), BitVec.add_assoc,
      ← BitVec.ofNat_add] at he
    exact he.symm
  refine {
    saved := ?_
    rbx := (hslot 16 (by decide)).trans h.rbx
    r14 := (hslot 8 (by decide)).trans h.r14
    returnSlot := ?_
    memory := memoryWriteFrame_trans h.memory (ha.memoryWriteFrame ?_)
    grows := fun a hx ↦ ha.grow a (h.grows a hx)
    rest := (ha.scalarFrame_eq (by rfl)).trans h.rest }
  · intro r hr
    apply (hsaved r ?_).trans (h.saved r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · have hz := hslot 0 (by decide)
    simp only [BitVec.sub_zero] at hz
    exact hz.trans h.returnSlot
  · apply Memcpy.clobbers_writesWithin
    intro i hi
    exact ⟨⟨(initial.regValue .rsi).toNat, v.digestBytes fullState⟩,
      by simp [writeRegions], region_contains_byte hp.outputRead.low hi⟩

theorem BodyFrame.after_memcpy_frame {boundary : ReturnBoundary} {v : Variant}
    {reset keccak fullState : Bool} {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre boundary v reset state initial keccak fullState)
    (h : BodyFrame v initial s fullState)
    (ha : AgreesExcept (Memcpy.clobbers (initial.regValue .rsi)
      (v.digestBytes fullState)) s t)
    (hsp : stackPtr t = stackPtr s) : BodyFrame v initial t fullState := by
  refine { h.toSavedFrame.after_memcpy_frame hp ha with
    stack := hsp.trans h.stack
    stateSaved := (ha.read (n := 64) (r := 3) (by simp [Memcpy.clobbers])).trans h.stateSaved
    output := (ha.read (n := 64) (r := 14) (by simp [Memcpy.clobbers])).trans h.output }

theorem Permuted.state_bytes {boundary : ReturnBoundary} {v : Variant}
    {reset keccak fullState : Bool} {state : Incremental.State} {initial s : RamState}
    (hp : CallPre boundary v reset state initial keccak fullState)
    (h : Permuted v reset state initial s keccak fullState) :
    Bytes s.external (initial.regValue .rdi) (v.digestBytes fullState)
      (fun i ↦ (digest v state keccak fullState)[i]!) := by
  intro i hi
  have hb := (h.toSavedFrame.readable hp.stateRead).mem i
    (Nat.lt_of_lt_of_le hi (Nat.le_trans (v.digestBytes_le_state fullState) (by decide)))
  obtain ⟨byte, hbyte⟩ := Option.isSome_iff_exists.mp hb
  have he := LaneMemory.storedByte_memoryLanes (initial.regValue .rdi) s
    ⟨i / 8, by have := v.digestBytes_le_state fullState; omega⟩ ⟨i % 8, by omega⟩
  rw [h.lanes] at he
  have hi' : 8 * (i / 8) + i % 8 = i := by omega
  simp only [hi', memByte] at he
  change _ = (s.external[initial.regValue .rdi + BitVec.ofNat 64 i]?).getD 0 at he
  rw [hbyte] at he
  rw [hbyte]
  congr 1
  change byte = (digest v state keccak fullState)[i]!
  rw [getElem!_pos (digest v state keccak fullState) i hi]
  exact he.symm.trans (LaneMemory.getElem_digestLanes_eq_storedByte _ _ _ i hi).symm

theorem full_output_image (reset : Bool) :
    ∀ x ∈ codeRange (outputAddress .sha256 reset true true) Output.outputFullBytes,
      x ∈ Extracted.programImage := by
  have h : ∀ i : Fin Output.outputFullBytes.length,
      Extracted.programSections.fetchByte
        (outputAddress .sha256 reset true true + BitVec.ofNat 64 i.val) =
          some Output.outputFullBytes[i.val] := by
    cases reset <;> decide +kernel
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact imageSections_mem_toCodeMap_of_fetchByte (h i)

theorem full_output_advance [Bindings] {boundary : ReturnBoundary} {reset : Bool}
    {state : Incremental.State} {initial : RamState}
    (hp : CallPre boundary .sha256 reset state initial true true)
    (hb : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 3 (Permuted .sha256 reset state initial · true true)
      Extracted.programImage (fun _ t ↦
        BodyFrame .sha256 initial t true ∧
        t.RIP = outputAddress .sha256 reset true true + (11 : BitVec 64) ∧
        (Operand.reg 7 : Operand 64).read t = initial.regValue .rsi ∧
        (Operand.reg 6 : Operand 64).read t = initial.regValue .rdi ∧
        (Operand.reg 2 : Operand 64).read t = 200 ∧
        Bytes t.external (initial.regValue .rdi) 200
          (fun i ↦ (digest .sha256 state true true)[i]!)) := by
  intro s hs hc h
  have hn (offset : Nat) (ho : offset ≤ 11) :
      outputAddress .sha256 reset true true + BitVec.ofNat 64 offset ≠ boundary.rip := by
    intro he
    apply hb
    rw [← he]
    have haddr : outputAddress .sha256 reset true true = Extracted.textAddress +
        BitVec.ofNat 64 ((outputAddress .sha256 reset true true).toNat -
          Extracted.textAddress.toNat) := by cases reset <;> decide +kernel
    have hsize : (outputAddress .sha256 reset true true).toNat -
        Extracted.textAddress.toNat + 11 < Extracted.textBytes.size := by
      cases reset <;> decide +kernel
    rw [haddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Permutation.inProgram_text_offset _ (by omega)
  obtain ⟨t, ht, hr, hct, he⟩ := Output.outputFull_advance
    (outputAddress .sha256 reset true true) (initial.regValue .rdi)
    (initial.regValue .rsi) boundary Extracted.programImage (full_output_image reset) hn
    s hs hc (h.toBodyFrame.output_pre hp h.rip)
  have ha : AgreesExcept (Memcpy.clobbers (initial.regValue .rsi) 200) s t :=
    he.agrees.mono (by
      simp [Output.outputFullEffect, Effect.components, Write.component,
        Operand.component, Memcpy.clobbers])
  have hsp : stackPtr t = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
    simp [Output.outputFullEffect, Effect.components, Write.component, Operand.component])
  have hm : t.external = s.external := he.agrees.external (by
    simp [Output.outputFullEffect, Effect.components, Write.component,
      Operand.component, Component.Covers])
  exact ⟨t, ht, hr, hct, h.toBodyFrame.after_memcpy_frame hp ha hsp,
    he.rip, he.writes.2.1, he.writes.2.2, he.writes.1, hm ▸ h.state_bytes hp⟩

theorem CallPre.full_memcpy_separate {boundary : ReturnBoundary} {reset : Bool}
    {state : Incremental.State} {initial : RamState}
    (hp : CallPre boundary .sha256 reset state initial true true) :
    (initial.regValue .rdi).toNat + 200 ≤ (initial.regValue .rsi).toNat ∨
      (initial.regValue .rsi).toNat + 200 ≤ (initial.regValue .rdi).toNat := by
  apply Classical.byContradiction
  intro hn
  have hlo := hp.outputRead.low
  have hls := hp.stateRead.low
  change (initial.regValue .rsi).toNat + 200 ≤ 2 ^ 32 at hlo
  by_cases hle : (initial.regValue .rsi).toNat ≤ (initial.regValue .rdi).toNat
  · apply hp.outputState ((initial.regValue .rdi).toNat - (initial.regValue .rsi).toNat)
      (by change _ < 200; omega) 0 (by decide)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · apply hp.outputState 0 (by decide)
      ((initial.regValue .rsi).toNat - (initial.regValue .rdi).toNat) (by omega)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem full_finish_plain_advance [bindings : Bindings]
    (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {state : Incremental.State} {initial : RamState}
    (hp : CallPre boundary .sha256 false state initial true true)
    (hb : ¬ InProgram boundary.rip) (hinside : initial.regValue .rsp ≠ boundary.rsp) :
    AdvanceTriple boundary (7 + Memcpy.memcpy200Steps (initial.regValue .rsi))
      (Permuted .sha256 false state initial · true true) Extracted.programImage
      (fun _ t ↦ CallResult .sha256 false state initial t true true) := by
  intro s hs hc h
  obtain ⟨a, hsa, hra, hca, hf, hip, hdst, hsrc, hlen, hbytes⟩ :=
    full_output_advance hp hb s hs hc h
  have hpre : FinalizeEpiloguePrefixPre 0x10646e (initial.regValue .rsp + 8) a := by
    refine ⟨hip, ?_, ?_⟩
    · change stackPtr a = _
      rw [show stackPtr a = initial.regValue .rsp - 24 from hf.stack]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro i
      have he : initial.regValue .rsp + 8 - 24 =
          frameBase initial + BitVec.ofNat 64 280 := by
        simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hf.toSavedFrame.readable (readable_slice hp.frameRead (280 + 8 * i.val) 8
        (by have := i.isLt; omega))
  have prefixcode : ∀ x ∈ codeRange 0x10646e finalizeEpiloguePrefixBytes,
      x ∈ Extracted.programImage :=
    textSlice_subset_programImage (offset := 0x646e) (len := 7)
      (by decide +kernel) (by decide +kernel)
  have prefixboundary : ∀ x ∈ [(0x10646e : BitVec 64) + 4, 0x10646e + 5, 0x10646e + 7],
      x ≠ boundary.rip := by
    intro x hx he
    apply hb
    rw [← he]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Permutation.inProgram_text_offset 0x6472 (by decide +kernel)
    · exact Permutation.inProgram_text_offset 0x6473 (by decide +kernel)
    · exact Permutation.inProgram_text_offset 0x6475 (by decide +kernel)
  obtain ⟨b, hab, hrb, hcb, he⟩ := finalizeEpiloguePrefix_advance boundary 0x10646e
    (initial.regValue .rsp + 8) prefixcode prefixboundary a hra hca hpre
  have loaded : ProgramLoaded b := fun addr byte hbyte ↦ (hcb (addr, byte) hbyte).2
  have hgot := Memcpy.memcpyPointer_read loaded
  have hgotread := Memcpy.memcpyPointer_readable loaded
  have jumpcode : ∀ x ∈ codeRange 0x106475 ([0xff, 0x25] ++ immBytes 32 0xf9d05),
      x ∈ Extracted.programImage :=
    textSlice_subset_programImage (offset := 0x6475) (len := 6)
      (by decide +kernel) (by decide +kernel)
  have hjpre : b.RIP = 0x106475 ∧ MemReadable b 0x200180 8 ∧
      ((Operand.mem 0x200180 : Operand 64).read b).toNat < 2^32 :=
    ⟨he.rip, hgotread, by rw [hgot]; decide +kernel⟩
  have hjne : (Operand.mem 0x200180 : Operand 64).read b ≠ boundary.rip := by
    rw [hgot]
    exact fun heq ↦ hb (heq ▸ Permutation.inProgram_text_offset 0x6a70 (by decide +kernel))
  obtain ⟨c, hbc, hrc, hj⟩ := (jmp_m64_rip_effect_step 0x106475 0xf9d05).advances
    hrb (hcb.mono jumpcode) hjpre hjne
  have hjframe : AgreesExcept [Component.rip] b c := hj.agrees
  have hjmem : c.external = b.external := hjframe.external (by simp [Component.Covers])
  have hcmem : c.external = a.external := hjmem.trans he.memory
  have hcc := hcb.of_external_eq hjmem
  have hac : AgreesExcept epilogueChanges a c := epilogueChanges_trans he.agrees
    (hjframe.mono (by simp [epilogueChanges]))
  have csp : stackPtr c = initial.regValue .rsp := by
    have hjsp := hjframe.read (n := 64) (r := 4) (by simp)
    change stackPtr c = stackPtr b at hjsp
    exact hjsp.trans (by simpa only [BitVec.add_sub_cancel] using he.stack)
  have cdst : (Operand.reg 7 : Operand 64).read c = initial.regValue .rsi :=
    (hac.read (by simp [epilogueChanges])).trans hdst
  have csrc : (Operand.reg 6 : Operand 64).read c = initial.regValue .rdi :=
    (hac.read (by simp [epilogueChanges])).trans hsrc
  have clen : (Operand.reg 2 : Operand 64).read c = 200 :=
    (hac.read (by simp [epilogueChanges])).trans hlen
  have ctop : stackTop c = stackTop initial := by
    change memLoad c.external (stackPtr c) 64 = _
    rw [csp, hcmem]
    exact hf.returnSlot
  have csaved : CalleeSavedRegistersUnchanged initial c := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · have hr := (hjframe.read (n := 64) (r := 3) (by simp)).trans he.rbx
      have ha : initial.regValue .rsp + 8 - 24 = initial.regValue .rsp - 16 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
      rw [ha] at hr
      exact hr.trans hf.rbx
    · exact (hac.read (n := 64) (r := 5) (by simp [epilogueChanges])).trans (hf.saved .rbp (by simp))
    · exact (hac.read (n := 64) (r := 12) (by simp [epilogueChanges])).trans (hf.saved .r12 (by simp))
    · exact (hac.read (n := 64) (r := 13) (by simp [epilogueChanges])).trans (hf.saved .r13 (by simp))
    · have hr := (hjframe.read (n := 64) (r := 14) (by simp)).trans he.r14
      have ha : initial.regValue .rsp + 8 - 16 = initial.regValue .rsp - 8 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
      rw [ha] at hr
      exact hr.trans hf.r14
    · exact (hac.read (n := 64) (r := 15) (by simp [epilogueChanges])).trans (hf.saved .r15 (by simp))
  have cpre : Memcpy.Pre boundary c 200 false := by
    refine ⟨?_, clen, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hj.rip.trans hgot
    · exact directionFlagUnset_of_fixedPart ((hac.scalarFrame_eq (by rfl)).trans hf.rest) hp.direction
    · rw [csrc]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        (hf.toSavedFrame.readable (readable_slice hp.stateRead 0 200 (by decide))).of_external_eq hcmem
    · rw [cdst]
      exact (hf.toSavedFrame.readable hp.outputRead).of_external_eq hcmem
    · rw [csrc, cdst]
      exact hp.full_memcpy_separate
    · rw [cdst]
      intro address hin ht
      obtain ⟨i, hi, heq⟩ := region_contains_offset hin
      exact hp.outputAvoid i hi (.inr (heq ▸ ht))
    · rw [cdst]
      intro address hin ht
      obtain ⟨i, hi, heq⟩ := region_contains_offset hin
      exact hp.outputAvoid i hi (.inl (heq ▸ ht))
    · rw [csp]
      have hh := hf.toSavedFrame.readable (readable_slice hp.frameRead 296 8 (by decide))
      have heq : frameBase initial + BitVec.ofNat 64 296 = initial.regValue .rsp :=
        BitVec.sub_add_cancel _ _
      rw [heq] at hh
      exact hh.of_external_eq hcmem
    · rw [ctop]
      obtain ⟨byte, hh⟩ := hp.target
      exact (hc (stackTop initial, byte) hh).1
    · rw [cdst, csp]
      intro i hi j hj heq
      apply hp.outputStack i hi (296 + j) (by omega)
      have heq' : initial.regValue .rsp = frameBase initial + BitVec.ofNat 64 296 :=
        (BitVec.sub_add_cancel _ _).symm
      rw [heq', BitVec.add_assoc, ← BitVec.ofNat_add] at heq
      exact heq
    · exact csp ▸ hinside
    · left
      rw [ctop]
      exact fun heq ↦ hb (heq ▸ hp.target)
  obtain ⟨t, hct, ht⟩ := Memcpy.memcpy200_steps hstride boundary c hrc hcc cpre
  have hcount : Memcpy.memcpy200Steps ((Operand.reg 7 : Operand 64).read c) =
      Memcpy.memcpy200Steps (initial.regValue .rsi) := congrArg _ cdst
  rw [hcount] at hct
  refine ⟨t, ?_, ht.ready, ht.code, ?_⟩
  · simpa only [← Nat.add_assoc] using hsa.trans (hab.trans (hbc.trans hct))
  · refine {
      rip := ht.rip.trans ctop
      stack := ht.rsp.trans (congrArg (· + (8 : BitVec 64)) csp)
      saved := ?_
      memory := ?_
      grows := ?_
      rest := (ht.agrees.scalarFrame_eq (by rfl)).trans ((hac.scalarFrame_eq (by rfl)).trans hf.rest)
      output := ?_
      zero := fun hfalse ↦ Bool.noConfusion hfalse }
    · have hsaved : CalleeSavedRegistersUnchanged c t :=
        calleeSavedRegistersUnchanged_of_agreesExcept ht.agrees (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) [Memcpy.clobbers])
      exact fun r hr ↦ (hsaved r hr).trans (csaved r hr)
    · have hframe : MemoryWriteFrame initial c (writeRegions .sha256 initial true) := by
        intro address ha
        rw [hcmem]
        exact hf.memory address ha
      apply memoryWriteFrame_trans hframe
      apply ht.agrees.memoryWriteFrame
      rw [cdst]
      apply Memcpy.clobbers_writesWithin
      intro i hi
      exact ⟨⟨(initial.regValue .rsi).toNat, 200⟩, by simp [writeRegions, Variant.digestBytes],
        region_contains_byte hp.outputRead.low hi⟩
    · intro address ha
      apply ht.agrees.grow
      rw [hcmem]
      exact hf.grows address ha
    · intro i
      have hcop := ht.copy i.val i.isLt
      rw [cdst, csrc, hcmem, hbytes i.val i.isLt] at hcop
      change t.external[initial.regValue .rsi + BitVec.ofNat 64 i.val]? =
        some ((digest .sha256 state true true)[i.val]!) at hcop
      rw [getElem!_pos (digest .sha256 state true true) i.val i.isLt] at hcop
      exact hcop

end Sha3.Proofs.Finalize
