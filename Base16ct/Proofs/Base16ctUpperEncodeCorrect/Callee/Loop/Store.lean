import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Support
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Memory
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.LoopInstructions

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem output_prefix_extend {s t : RamState} {base : BitVec 64} {offset : Nat}
    {value : Nat → UInt8} (hbound : offset + 1 ≤ 2^64)
    (hw : MemWritable s (base + BitVec.ofNat 64 offset) 1)
    (hf : AgreesExcept [.mem (base + BitVec.ofNat 64 offset) 1, .rip] s t)
    (hr : (Operand.mem (base + BitVec.ofNat 64 offset) : Operand 8).read t =
      (value offset).toBitVec) (hp : Bytes s.external base offset value) :
    Bytes t.external base (offset + 1) value := by
  have ha : RangeApart (base + BitVec.ofNat 64 offset) 1 base offset := by
    simpa only [BitVec.add_zero] using
      RangeApart.offsets base (a := offset) (len := 1) (b := 0) (count := offset)
        hbound (by omega) (.inr (by omega))
  have hp' : Bytes t.external base offset value := by
    apply hp.of_agreesExcept hf
    intro i hi component hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := hcover
      exact ha j hj i hi he.symm
    · exact hcover
  have hm : ∀ i < 8 / 8,
      (t.external[base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ hf.grow _ (hw.mem i hi)
  have hb := Bytes.of_memLoad (n := 8) hm
  change memLoad t.external (base + BitVec.ofNat 64 offset) 8 = _ at hr
  rw [hr] at hb
  apply (hp'.append hb).congr
  intro i hi
  by_cases hil : i < offset
  · simp only [hil, ite_true]
  · have he : i = offset := by omega
    subst i
    simp [storedByte]


theorem output_store_step [Bindings] (c : CallContext) {s : RamState} (hs : RunInvariant c s)
    {p : BitVec 64} {len offset : Nat} {addr : RamState → BitVec 64}
    {value : RamState → BitVec 8} {code : X86.UserProcess.CodeMap}
    (step : StepEffect (StorePre p len addr 1) code (storeEffect p len addr value))
    (hcode : CodeIn code s) (hpre : StorePre p len addr 1 s)
    (hne : p + BitVec.ofNat 64 len ≠ (returnBoundary c.initial).rip)
    (haddr : addr s = c.initial.regValue .rcx + BitVec.ofNat 64 offset)
    (hc : 2 * c.input.length ≤ c.capacity) (hoff : offset < 2 * c.input.length)
    (hp : Bytes s.external (c.initial.regValue .rcx) offset
      (fun j ↦ (encodedBytes c.input).getD j 0))
    (hv : value s = ((encodedBytes c.input).getD offset 0).toBitVec) :
    ∃ t, Advances (returnBoundary c.initial) 1 s t ∧ RunInvariant c t ∧
      t.RIP = p + BitVec.ofNat 64 len ∧
      AgreesExcept [.mem (c.initial.regValue .rcx + BitVec.ofNat 64 offset) 1, .rip] s t ∧
      Bytes t.external (c.initial.regValue .rcx) (offset + 1)
        (fun j ↦ (encodedBytes c.input).getD j 0) := by
  obtain ⟨t, ha, ht, he⟩ := step.advances hs.ready hcode hpre hne
  have hf : AgreesExcept [.mem (c.initial.regValue .rcx + BitVec.ofNat 64 offset) 1,
      .rip] s t := by
    simpa only [storeEffect_components, haddr] using he.agrees
  have hw := hpre.write
  rw [haddr] at hw
  have hr : (Operand.mem (c.initial.regValue .rcx + BitVec.ofNat 64 offset) : Operand 8).read t =
      ((encodedBytes c.input).getD offset 0).toBitVec := by
    simpa only [storeEffect, Write.AllHold, haddr, hv] using he.writes
  have hbound : offset + 1 ≤ 2^64 := by
    have hb : (c.initial.regValue .rcx).toNat + c.capacity < 2^32 := c.valid.outputInMemory.2.1
    omega
  exact ⟨t, ha, hs.of_agrees c ht (output_store_widen c hc (by omega) hf), he.rip, hf,
    output_prefix_extend hbound hw hf hr hp⟩

theorem store_high_address {s : RamState} {base : BitVec 64} {i : Nat}
    (hbase : s.regValue .rcx = base) (hi : s.regValue .r8 = BitVec.ofNat 64 i) :
    storeAddrAt 0x1006a4 (.sib 1 (some 8) 1 .none) 4 s = base + BitVec.ofNat 64 (2 * i) := by
  change s.regValue .rcx + (s.regValue .r8 <<< 1) + BitVec.ofNat 64 0 = _
  rw [hbase, hi, BitVec.add_zero]
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change base + BitVec.ofNat 64 i * BitVec.ofNat 64 2 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm i 2]

theorem store_low_address {s : RamState} {base : BitVec 64} {i : Nat}
    (hbase : s.regValue .rcx = base) (hi : s.regValue .r8 = BitVec.ofNat 64 i) :
    storeAddrAt 0x1006c4 (.sib 1 (some 8) 1 (.d8 1)) 5 s =
      base + BitVec.ofNat 64 (2 * i + 1) := by
  change s.regValue .rcx + (s.regValue .r8 <<< 1) + 1 = _
  rw [hbase, hi, BitVec.shiftLeft_eq_mul_twoPow]
  change base + BitVec.ofNat 64 i * BitVec.ofNat 64 2 + BitVec.ofNat 64 1 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm i 2, BitVec.add_assoc, ← BitVec.ofNat_add]


theorem store_high_step [Bindings] (c : CallContext) {s : RamState} {i : Nat}
    (hs : RunInvariant c s) (hip : s.RIP = 0x1006a4)
    (hdst : s.regValue .rcx = c.initial.regValue .rcx)
    (hindex : s.regValue .r8 = BitVec.ofNat 64 i) (hc : 2 * c.input.length ≤ c.capacity) (hoff : 2 * i < 2 * c.input.length)
    (hp : Bytes s.external (c.initial.regValue .rcx) (2 * i)
      (fun j ↦ (encodedBytes c.input).getD j 0))
    (hv : (Operand.reg 11 : Operand 8).read s =
      ((encodedBytes c.input).getD (2 * i) 0).toBitVec) :
    ∃ t, Advances (returnBoundary c.initial) 1 s t ∧ RunInvariant c t ∧
      t.RIP = 0x1006a8 ∧
      AgreesExcept [.mem (c.initial.regValue .rcx + BitVec.ofNat 64 (2 * i)) 1, .rip] s t ∧
      Bytes t.external (c.initial.regValue .rcx) (2 * i + 1)
        (fun j ↦ (encodedBytes c.input).getD j 0) := by
  have haddr := store_high_address hdst hindex
  have hcode := program_text_slice hs.code 0x6a4 4 (by decide +kernel)
  have hb : Extracted.textBytes.toListFrom 0x6a4 4 = [0x46, 0x88, 0x1c, 0x41] := by
    decide +kernel
  rw [hb] at hcode
  apply output_store_step c hs (len := 4) (mov_m8_r11b_effect_step 0x1006a4) hcode
    ⟨hip, ?_, ?_⟩ (callee_ne_return c 0x6a8 (by decide +kernel)) haddr hc hoff hp hv
  · rw [haddr]
    exact hs.output_byte_writable c _ (by omega)
  · rw [haddr]
    exact output_rangeApart_text c (2 * i) 0x6a4 4 (by omega) (by decide +kernel)

theorem store_low_step [Bindings] (c : CallContext) {s : RamState} {i : Nat}
    (hs : RunInvariant c s) (hip : s.RIP = 0x1006c4)
    (hdst : s.regValue .rcx = c.initial.regValue .rcx)
    (hindex : s.regValue .r8 = BitVec.ofNat 64 i) (hc : 2 * c.input.length ≤ c.capacity) (hoff : 2 * i + 1 < 2 * c.input.length)
    (hp : Bytes s.external (c.initial.regValue .rcx) (2 * i + 1)
      (fun j ↦ (encodedBytes c.input).getD j 0))
    (hv : (Operand.reg 10 : Operand 8).read s =
      ((encodedBytes c.input).getD (2 * i + 1) 0).toBitVec) :
    ∃ t, Advances (returnBoundary c.initial) 1 s t ∧ RunInvariant c t ∧
      t.RIP = 0x1006c9 ∧
      AgreesExcept [.mem (c.initial.regValue .rcx + BitVec.ofNat 64 (2 * i + 1)) 1, .rip] s t ∧
      Bytes t.external (c.initial.regValue .rcx) (2 * i + 1 + 1)
        (fun j ↦ (encodedBytes c.input).getD j 0) := by
  have haddr := store_low_address hdst hindex
  have hcode := program_text_slice hs.code 0x6c4 5 (by decide +kernel)
  have hb : Extracted.textBytes.toListFrom 0x6c4 5 = [0x46, 0x88, 0x54, 0x41, 0x01] := by
    decide +kernel
  rw [hb] at hcode
  apply output_store_step c hs (len := 5) (mov_m8_r10b_effect_step 0x1006c4) hcode
    ⟨hip, ?_, ?_⟩ (callee_ne_return c 0x6c9 (by decide +kernel)) haddr hc hoff hp hv
  · rw [haddr]
    exact hs.output_byte_writable c _ (by omega)
  · rw [haddr]
    exact output_rangeApart_text c (2 * i + 1) 0x6c4 5 (by omega) (by decide +kernel)

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
