import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Frame
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Common.Encoding.Serialize.Store32
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mov_m32_r32_no_rex_effect_step)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem offset_covers {base : BitVec 64} {i : Nat} (h : scratchOffset i) :
    ∃ c ∈ components base, c.Covers (base + BitVec.ofNat 64 i) := by
  rcases h with h | h | h | h | h | h
  · refine ⟨.mem (base + 8) 8, by simp [components], i - 8, by omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add, Nat.add_sub_cancel' h.1]
  · refine ⟨.mem (base + 0x10) 0x68, by simp [components], i - 0x10, by omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add, Nat.add_sub_cancel' h.1]
  · refine ⟨.mem (base + 0x7c) 4, by simp [components], i - 0x7c, by omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add, Nat.add_sub_cancel' h.1]
  · refine ⟨.mem (base + 0x10) 32, by simp [components], i - 0x10, by omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add, Nat.add_sub_cancel' h.1]
  · refine ⟨.mem (base + 0x2d0) 8, by simp [components], i - 0x2d0, by omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add, Nat.add_sub_cancel' h.1]
  · refine ⟨.mem (base + 0x2e8) 16, by simp [components], i - 0x2e8, by omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add, Nat.add_sub_cancel' h.1]

theorem store_agrees {s t : RamState} {base : BitVec 64} {offset len : Nat}
    (h : AgreesExcept [.mem (base + BitVec.ofNat 64 offset) len, .rip] s t)
    (hoff : ∀ i < len, scratchOffset (offset + i)) :
    AgreesExcept (components base) s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hn hmem
    apply h.agree c _ hmem
    intro hc
    apply hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · contradiction
    · simp [components]
  · intro a hn
    apply h.memory a
    intro c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcover
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hn
      obtain ⟨d, hd, hv⟩ := offset_covers (hoff i hi)
      exact hn d hd hv
    · exact False.elim hcover

theorem load_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (pc : Nat) (rex : UInt8) (reg : BitVec 3) (am : AddrMode) (offset : Nat)
    (hr : RexWPrefix rex.toBitVec) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (ha : ∀ u : RamState, am.addr u (Extracted.textAddress + BitVec.ofNat 64 pc +
      BitVec.ofNat 64 (movLoadLen am)) = u.regValue .rsp + BitVec.ofNat 64 offset)
    (hreg : gprNumber 0 (rexR rex.toBitVec) reg ≠ 4)
    (hoff : offset ≤ 1416)
    (hpc : pc + movLoadLen am < 118431)
    (hbytes : Extracted.textBytes.toListFrom pc (rex :: 0x8b :: am.modrm reg :: am.tail).length =
      rex :: 0x8b :: am.modrm reg :: am.tail)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Advances boundary 1 t u ∧ ExponentFrame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (movLoadLen am) ∧
      (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 offset) : Operand 64).read t ∧
      AgreesExcept [.reg (gprNumber 0 (rexR rex.toBitVec) reg), .rip] t u := by
  have hc := programText_slice (programLoaded_codeIn hf.loaded) pc _ (by
    have := am.tail_length_le
    simp only [List.length_cons]
    unfold movLoadLen at hpc
    omega) hbytes
  have haddr := (ha t).trans (congrArg (· + BitVec.ofNat 64 offset) hf.rsp)
  obtain ⟨u, he, hrdy, heff⟩ :=
    (mov_r64_m64_effect_step _ rex hr reg am hv hx hb).advances
      (readyToStep hf.machine hf.bindingsSupported) hc
      ⟨hip, haddr ▸ stack_readable h hf hoff (by omega)⟩ (by
        change Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (movLoadLen am) ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program h.outerBoundary (inProgram_of_textOffset _ hpc))
  have hsub : ∀ c ∈ [.reg (gprNumber 0 (rexR rex.toBitVec) reg), .rip],
      c ∈ components (exponentFrameBase s) := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have hn : ∀ (a : BitVec 1) (b : BitVec 3), gprNumber 0 a b ≠ 4 →
          gprNumber 0 a b ∈ ([0,1,2,3,5,6,7,8,9,10,11,12,13,14,15] : List (BitVec 5)) := by
        decide +kernel
      simpa [components] using hn (rexR rex.toBitVec) reg hreg
    · simp [components]
  refine ⟨u, he, frame_of_agrees h hf hrdy (heff.agrees.mono hsub), heff.rip, ?_, heff.agrees⟩
  have hw := heff.writes
  change (Operand.reg _ : Operand 64).read u =
    (Operand.mem (am.addr t _) : Operand 64).read t at hw
  rwa [haddr] at hw

theorem store_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (pc : Nat) (rex : UInt8) (reg : BitVec 3) (am : AddrMode) (offset : Nat)
    (hr : RexWPrefix rex.toBitVec) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (ha : ∀ u : RamState, am.addr u (Extracted.textAddress + BitVec.ofNat 64 pc +
      BitVec.ofNat 64 (3 + am.tail.length)) = u.regValue .rsp + BitVec.ofNat 64 offset)
    (hoff : offset ≤ 1416) (halign : offset % 8 = 0)
    (hscratch : ∀ i < 8, scratchOffset (offset + i))
    (hpc : pc + (3 + am.tail.length) < 118431)
    (hbytes : Extracted.textBytes.toListFrom pc (rex :: 0x89 :: am.modrm reg :: am.tail).length =
      rex :: 0x89 :: am.modrm reg :: am.tail)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Advances boundary 1 t u ∧ ExponentFrame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (3 + am.tail.length) ∧
      (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 offset) : Operand 64).read u =
        (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read t ∧
      AgreesExcept [.mem (exponentFrameBase s + BitVec.ofNat 64 offset) 8, .rip] t u := by
  have hc := programText_slice (programLoaded_codeIn hf.loaded) pc _
    (by simp only [List.length_cons]; omega) hbytes
  have haddr := (ha t).trans (congrArg (· + BitVec.ofNat 64 offset) hf.rsp)
  obtain ⟨u, he, hrdy, heff⟩ :=
    (mov_m64_r64_effect_step _ rex hr reg am hv hx hb).advances
      (readyToStep hf.machine hf.bindingsSupported) hc
      ⟨hip, by simpa only [storeAddrAt, haddr] using
          stack_writable h hf hoff (by omega) (.inl ⟨rfl, halign⟩),
        by simpa only [storeAddrAt, haddr] using
          stack_apart_code h (codeOffset := pc) (codeLen := 3 + am.tail.length) hoff (by omega) (by omega)⟩ (by
        change Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 (3 + am.tail.length) ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program h.outerBoundary (inProgram_of_textOffset _ hpc))
  have heq : (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 pc)
      (gprNumber 0 (rexR rex.toBitVec) reg) am t).components =
      [.mem (exponentFrameBase s + BitVec.ofNat 64 offset) 8, .rip] := by
    rw [movM64R64Effect_components]
    change ([.mem (am.addr t _) 8, .rip] : List Component) = _
    rw [haddr]
  have hagree := heq ▸ heff.agrees
  refine ⟨u, he, frame_of_agrees h hf hrdy (store_agrees hagree hscratch), heff.rip, ?_, hagree⟩
  have hw := heff.writes
  change (Operand.mem (am.addr t _) : Operand 64).read u =
    (Operand.reg _ : Operand 64).read t at hw
  rwa [haddr] at hw

theorem word_of_store_apart {s t : RamState} {base a b : BitVec 64}
    (h : AgreesExcept [.mem (base + a) 8, .rip] s t)
    (ha : OffsetsApart a 8 b 8) :
    (Operand.mem (base + b) : Operand 64).read t =
      (Operand.mem (base + b) : Operand 64).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcover
    exact ha.ne base hj hi (by decide +kernel) he.symm
  · exact hcover

theorem word_of_registers {s t : RamState} {r : BitVec 5} {address : BitVec 64}
    (h : AgreesExcept [.reg r, .rip] s t) :
    (Operand.mem address : Operand 64).read t = (Operand.mem address : Operand 64).read s :=
  P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h _ (by simp [Component.Covers])

theorem word_of_store32_apart {s t : RamState} {base a b : BitVec 64}
    (h : AgreesExcept [.mem (base + a) 4, .rip] s t)
    (ha : OffsetsApart a 4 b 8) :
    (Operand.mem (base + b) : Operand 64).read t =
      (Operand.mem (base + b) : Operand 64).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcover
    exact ha.ne base hj hi (by decide +kernel) he.symm
  · exact hcover

theorem save_counter [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x115510) :
    ∃ u, Advances boundary 1 t u ∧ ExponentFrame s u ∧ u.RIP = 0x115514 ∧
      (Operand.mem (exponentFrameBase s + 0x7c) : Operand 32).read u =
        (Operand.reg 0 : Operand 32).read t ∧
      AgreesExcept [.mem (exponentFrameBase s + 0x7c) 4, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 0x7c)
  have haddr : storeAddrAt 0x115510 am 4 t = exponentFrameBase s + 0x7c := by
    change t.regValue .rsp + 0x7c = _
    rw [hf.rsp]
  obtain ⟨u, he, hr, hw⟩ :=
    (mov_m32_r32_no_rex_effect_step 0x115510 0 am (by decide) rfl rfl).advances
      (readyToStep hf.machine hf.bindingsSupported)
      (programText_slice (programLoaded_codeIn hf.loaded) 0x15510 _ (by decide) (by decide +kernel))
      (by
        refine ⟨hip, ?_, ?_⟩
        · change MemWritable t (t.regValue .rsp + 0x7c) 4
          rw [hf.rsp]
          exact stack_writable h hf (offset := 0x7c) (len := 4)
            (by decide) (by decide) (.inr (.inl ⟨rfl, by decide⟩))
        · change RangeApart (t.regValue .rsp + 0x7c) 4 0x115510 4
          rw [hf.rsp]
          exact stack_apart_code h (offset := 0x7c) (len := 4)
            (codeOffset := 0x15510) (codeLen := 4) (by decide) (by decide) (by decide))
      (boundary_ne_program h.outerBoundary (inProgram_of_textOffset 0x15514 (by decide)))
  have ha : AgreesExcept [.mem (exponentFrameBase s + 0x7c) 4, .rip] t u := by
    have ha := hw.agrees
    x86_norm [am] at ha
    change AgreesExcept [.mem (t.regValue .rsp + 0x7c) 4, .rip] t u at ha
    rwa [hf.rsp] at ha
  refine ⟨u, he, frame_of_agrees h hf hr
    (store_agrees (offset := 0x7c) ha (by unfold scratchOffset; omega)), hw.rip, ?_, ha⟩
  have hv := hw.writes
  change (Operand.mem (storeAddrAt 0x115510 am 4 t) : Operand 32).read u =
    (Operand.reg 0 : Operand 32).read t at hv
  rwa [haddr] at hv

end P256.Proofs.Sec1.SquareRoot.SquareFour
