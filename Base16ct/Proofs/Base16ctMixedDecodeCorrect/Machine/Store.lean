import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_store [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002d8)
    (hWritable : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rcx + s.regValue .rax) 1)
    (hAvoid : ¬ InProgram (s.regValue .rcx + s.regValue .rax))
    (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x1002db ∧
      t.external[s.regValue .rcx + s.regValue .rax]? =
        some (UInt8.ofNat ((s.regValue .rbx).setWidth 8).toNat) ∧
      AgreesExcept [.mem (s.regValue .rcx + s.regValue .rax) 1, .rip] s t := by
  have hStep := Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte.mov_m8_r8_effect_step 0x1002d8 3
    (.sib 1 (some 0) 0 .none) (by decide) rfl rfl (by decide)
  have hBytes : CodeIn (codeRange 0x1002d8 [0x88, 0x1c, 0x01]) s :=
    program_text_slice hCode 0x2d8 3 (by decide +kernel)
  have hAddr : storeAddrAt 0x1002d8 (.sib 1 (some 0) 0 .none) 3 s =
      s.regValue .rcx + s.regValue .rax := by
    simp [storeAddrAt, AddrMode.addr, Disp.value]
    rfl
  have hAvoid' : ∀ i < 1,
      ¬ InProgram (s.regValue .rcx + s.regValue .rax + BitVec.ofNat 64 i) := by
    intro i hi
    have : i = 0 := by omega
    subst i
    simpa using hAvoid
  have hPre : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre 0x1002d8 3
      (storeAddrAt 0x1002d8 (.sib 1 (some 0) 0 .none) 3) 1 s := by
    refine ⟨hRip, hAddr ▸ hWritable, ?_⟩
    rw [hAddr]
    exact rangeApart_text (offset := 0x2d8) hAvoid' (by decide +kernel)
  obtain ⟨t, hRun, hReady', hEffect⟩ := hStep.advances hReady hBytes hPre
    (outsideMixed_ne (pc := 0x1002db) hOutside (by decide) (by decide))
  have hComponents :
      (storeEffect 0x1002d8 3 (storeAddrAt 0x1002d8 (.sib 1 (some 0) 0 .none) 3)
        (fun u ↦ (Operand.reg 3 : Operand 8).read u) s).components =
      [.mem (s.regValue .rcx + s.regValue .rax) 1, .rip] := by
    simp only [storeEffect_components, hAddr]
  have hAgrees : AgreesExcept [.mem (s.regValue .rcx + s.regValue .rax) 1, .rip] s t := by
    rw [← hComponents]
    exact hEffect.agrees
  have hRead : (Operand.mem (s.regValue .rcx + s.regValue .rax) : Operand 8).read t =
      (Operand.reg 3 : Operand 8).read s := by
    have hw := hEffect.writes
    change (Operand.mem (storeAddrAt 0x1002d8 (.sib 1 (some 0) 0 .none) 3 s) :
      Operand 8).read t = (Operand.reg 3 : Operand 8).read s at hw
    rwa [hAddr] at hw
  have hPresent : ∀ i < 8 / 8,
      (t.external[s.regValue .rcx + s.regValue .rax + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ hAgrees.grow _ (hWritable.bytes i hi)
  have hByte := Bytes.of_memLoad (n := 8) hPresent 0 (by decide)
  change memLoad t.external _ 8 = _ at hRead
  rw [hRead] at hByte
  refine ⟨t, hRun, hReady', hEffect.codeIn
    (store_avoids_program hComponents hAvoid') hCode, hEffect.rip, ?_, hAgrees⟩
  simp only [BitVec.add_zero] at hByte
  change t.external[s.regValue .rcx + s.regValue .rax]? =
    some (storedByte ((s.regValue .rbx).setWidth 8) 0) at hByte
  simpa [storedByte] using hByte

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
