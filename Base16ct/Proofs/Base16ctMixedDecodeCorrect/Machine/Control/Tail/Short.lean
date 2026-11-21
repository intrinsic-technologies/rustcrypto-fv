import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Tail.Return
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem tail_read_mem {s t : RamState} {cs : List Component}
    (he : AgreesExcept cs s t) {a : BitVec 64} {n : Nat}
    (h : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[a + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[a + BitVec.ofNat 64 i]?).getD 0
  rw [he.byte (h i hi)]

private theorem tail_read_frame {s t : RamState} {a b : BitVec 64} {len n : Nat}
    (h : AgreesExcept [.mem a len, .rip] s t) (ha : RangeApart a len b (n / 8)) :
    (Operand.mem b : Operand n).read t = (Operand.mem b : Operand n).read s := by
  apply tail_read_mem h
  intro i hi c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    exact ha j hj i hi he.symm
  · exact hv.elim

theorem mixed_success_return [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100300)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rdx) 8)
    (avoid : ∀ i < 8, ¬ InProgram (s.regValue .rdx + BitVec.ofNat 64 i))
    (apart : RangeApart (s.regValue .rdx) 8 (stackPtr s) 8)
    (hStack : MemReadable s (stackPtr s) 8)
    (hReturn : stackTop s = boundary.rip) (hRsp : stackPtr s + 8 = boundary.rsp)
    (hLow : boundary.rip.toNat < userAddressLimit) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Returns boundary 3 s t ∧ t.RIP = boundary.rip ∧ stackPtr t = boundary.rsp ∧
      ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (Operand.mem (s.regValue .rdx) : Operand 64).read t = s.regValue .r9 ∧
      t.regValue .rax = 0 ∧
      AgreesExcept [.mem (s.regValue .rdx) 8, .reg 0, .flags, .reg 4, .rip] s t := by
  have len : 3 + (AddrMode.base 2 .none).tail.length = 3 := rfl
  have addr : storeAddrAt 0x100300 (.base 2 .none) 3 s = s.regValue .rdx := by
    change s.regValue .rdx + 0 = s.regValue .rdx
    exact BitVec.add_zero _
  obtain ⟨a, ra, readyA, ea⟩ := (Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step
    0x100300 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.base 2 .none) (by decide) rfl rfl).advances
    hReady (program_text_slice hCode 0x300 3 (by decide +kernel))
    ⟨hRip, by rw [len, addr]; exact hw,
      by rw [len, addr]; exact rangeApart_text (offset := 0x300) (count := 3) avoid (by decide +kernel)⟩
    (outsideMixed_ne (pc := 0x100303) hOutside (by decide) (by decide))
  have fa : AgreesExcept [.mem (s.regValue .rdx) 8, .rip] s a := by
    simpa only [movM64R64Effect_components, len, addr] using ea.agrees
  have ca := CodeIn.of_agreesExcept fa (by
    intro x hx c hc hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, he⟩ := hv
      exact avoid i hi (he ▸ ⟨x.2, hx⟩)
    · exact hv) hCode
  obtain ⟨b, rb, readyB, eb⟩ := (xor_r32_r32_effect_step 0x100303 0xc0 (by decide)).advances
    readyA (program_text_slice ca 0x303 2 (by decide +kernel)) ea.rip
    (outsideMixed_ne (pc := 0x100305) hOutside (by decide) (by decide))
  have fb : AgreesExcept [.reg 0, .flags, .rip] a b := eb.agrees
  have cb := fb.codeIn (by simp [Component.Covers]) ca
  have spB : stackPtr b = stackPtr s := (fa.trans fb).read (n := 64) (r := 4) (by simp)
  have topB : stackTop b = boundary.rip := by
    change (Operand.mem (stackPtr b) : Operand 64).read b = _
    rw [spB, tail_read_mem fb (by simp [Component.Covers]), tail_read_frame fa apart]
    exact hReturn
  obtain ⟨t, rt, ripT, rspT, readyT, codeT, ft⟩ := common_return readyB cb
    (Or.inr (Or.inl eb.rip))
    (by rw [spB]; exact Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.readable_of_agrees hStack (fa.trans fb))
    topB (by rw [spB]; exact hRsp) hLow
  refine ⟨t, ra.returns (rb.returns rt), ripT, rspT, readyT, codeT, ?_, ?_, ?_⟩
  · rw [tail_read_mem ft (by simp [Component.Covers]), tail_read_mem fb (by simp [Component.Covers])]
    have h := ea.writes
    change (Operand.mem (s.regValue .rdx + 0) : Operand 64).read a = s.regValue .r9 at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · have hz : b.regValue .rax = 0 := by
      have h := eb.writes
      change b.regValue .rax =
        (((Operand.reg 0 : Operand 32).read a) ^^^ (Operand.reg 0 : Operand 32).read a).setWidth 64 at h
      simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using h
    exact (ft.read (n := 64) (r := 0) (by simp)).trans hz
  · exact ((fa.trans fb).trans ft).mono (by simp [or_left_comm, or_comm])

theorem mixed_error_return [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100306)
    (hStack : MemReadable s (stackPtr s) 8)
    (hReturn : stackTop s = boundary.rip) (hRsp : stackPtr s + 8 = boundary.rsp)
    (hLow : boundary.rip.toNat < userAddressLimit) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Returns boundary 2 s t ∧ t.RIP = boundary.rip ∧ stackPtr t = boundary.rsp ∧
      ReadyToStep t ∧ CodeIn Extracted.programImage t ∧ t.regValue .rax = 2 ∧
      AgreesExcept [.reg 0, .reg 4, .rip] s t := by
  obtain ⟨a, ra, readyA, ea⟩ := (mov_r32_imm32_effect_step 0x100306 0xb8 (by decide) 2).advances
    hReady (program_text_slice hCode 0x306 5 (by decide +kernel)) hRip
    (outsideMixed_ne (pc := 0x10030b) hOutside (by decide) (by decide))
  have fa : AgreesExcept [.reg 0, .rip] s a := ea.agrees
  have ca := fa.codeIn (by simp [Component.Covers]) hCode
  have spA : stackPtr a = stackPtr s := fa.read (n := 64) (r := 4) (by simp)
  have memA := fa.external (by simp [Component.Covers])
  obtain ⟨t, rt, ripT, rspT, readyT, codeT, ft⟩ := common_return readyA ca
    (Or.inr (Or.inr ea.rip)) (by rw [spA]; exact hStack.of_external_eq memA)
    (by simpa only [stackTop, spA, Operand.read, memA] using hReturn)
    (by rw [spA]; exact hRsp) hLow
  exact ⟨t, ra.returns rt, ripT, rspT, readyT, codeT,
    (ft.read (n := 64) (r := 0) (by simp)).trans ea.writes,
    (fa.trans ft).mono (by simp [or_left_comm, or_comm])⟩

theorem mixed_empty_tail [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002fb) (hNonzero : s.regValue .rcx ≠ 0) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100300 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (test_r64_r64_effect_step 0x1002fb 0x48 0xc9
      (by unfold RexWPrefix; decide) (by decide)).advances
      hReady (program_text_slice hCode 0x2fb 3 (by decide +kernel)) hRip
      (outsideMixed_ne (pc := 0x1002fe) hOutside (by decide) (by decide))
  have frameA : AgreesExcept [.flags, .rip] s a := effectA.agrees
  have codeA := frameA.codeIn (by simp [Component.Covers]) hCode
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (s.regValue .rcx == 0) := by
    have hz := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
      ((s.regValue .rcx &&& s.regValue .rcx) == 0) at hz
    simpa only [BitVec.and_self] using hz
  have next : (jccEffect 0x1002fe 2 4 ((0x06 : BitVec 8).signExtend 64) a).rip =
      0x100300 := by
    simpa [jccEffect, branchEffect, branchTarget, condHolds, hz] using hNonzero
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (jcc_rel8_effect_step 0x1002fe 4 0x06).advances (boundary := boundary)
    readyA (program_text_slice codeA 0x2fe 2 (by decide +kernel))
    ⟨effectA.rip, fun _ ↦ by decide⟩ (by
      rw [next]
      exact outsideMixed_ne hOutside (by decide) (by decide))
  have frameT : AgreesExcept [.rip] a t := effectT.agrees
  exact ⟨t, runA.trans runT, readyT, frameT.codeIn (by simp [Component.Covers]) codeA,
    effectT.rip.trans next, (frameA.trans frameT).mono (by simp)⟩

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
