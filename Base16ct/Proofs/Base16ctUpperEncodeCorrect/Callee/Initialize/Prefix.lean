import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Initialize.State
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Initialize.Arithmetic
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Support
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem init_program_slice {s : RamState} (h : CodeIn Extracted.programImage s)
    (offset : Nat) (bytes : List UInt8)
    (he : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hb : offset + bytes.length ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (0x100000 + BitVec.ofNat 64 offset) bytes) s := by
  simpa only [he, Extracted.textAddress] using program_text_slice h offset bytes.length hb

theorem init_cmp_ule (x y : BitVec 64) :
    ((cmpSpec x y).CF || (cmpSpec x y).ZF) = decide (x ≤ y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, cmpSpec, subSpec, decide_eq_true_eq, beq_iff_eq,
    BitVec.sub_eq_iff_eq_add, BitVec.le_def]
  change (x.toNat < y.toNat ∨ x = BitVec.add 0#64 y) ↔ x.toNat ≤ y.toNat
  have hz : BitVec.add 0#64 y = y := BitVec.zero_add _
  rw [hz, ← BitVec.toNat_inj]
  omega

theorem callee_initialize_prefix [Bindings] (c : CallContext) {s : RamState}
    (hs : RunInvariant c s) (he : CalleeEntry c s) :
    ∃ t, Advances (returnBoundary c.initial) 4 s t ∧ InitializeState c t ∧
      t.RIP = if 2 * c.input.length ≤ c.capacity then 0x100668 else 0x10065c := by
  have hne (offset : Nat) (hb : offset < Extracted.textBytes.size) :
      0x100000 + BitVec.ofNat 64 offset ≠ (returnBoundary c.initial).rip :=
    callee_ne_return c offset hb
  have hc₁ : CodeIn (codeRange 0x100650 [0x48, 0x89, 0xf8]) s :=
    init_program_slice hs.code 0x650 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨s₁, ha₁, hr₁, he₁⟩ :=
    (mov_r64_r64_effect_step 0x100650 0x48 0xf8 (by unfold RexWPrefix; decide +kernel) rfl).advances
      hs.ready hc₁ he.rip (hne 0x653 (by decide +kernel))
  change (movR64R64Effect 0x100650 0 7 s).Holds s s₁ at he₁
  have hf₁ : AgreesExcept [.reg 0, .rip] s s₁ := he₁.agrees
  have code₁ := hf₁.codeIn (by simp [Component.Covers]) hs.code
  have hc₂ : CodeIn (codeRange 0x100653 [0x48, 0x8d, 0x3c, 0x12]) s₁ :=
    init_program_slice code₁ 0x653 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨s₂, ha₂, hr₂, he₂⟩ :=
    (lea_r64_effect_step 0x100653 0x48 (by unfold RexWPrefix; decide +kernel) 7
      (.sib 2 (some 2) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl).advances
      hr₁ hc₂ he₁.rip (hne 0x657 (by decide +kernel))
  change (leaR64Effect 0x100653 7 (.sib 2 (some 2) 0 .none) s₁).Holds s₁ s₂ at he₂
  have hf₂ : AgreesExcept [.reg 7, .rip] s₁ s₂ := he₂.agrees
  have code₂ := hf₂.codeIn (by simp [Component.Covers]) code₁
  have hc₃ : CodeIn (codeRange 0x100657 [0x4c, 0x39, 0xc7]) s₂ :=
    init_program_slice code₂ 0x657 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨s₃, ha₃, hr₃, he₃⟩ :=
    (cmp_r64_r64_effect_step 0x100657 0x4c 0xc7 (by unfold RexWPrefix; decide +kernel) rfl).advances
      hr₂ hc₃ he₂.rip (hne 0x65a (by decide +kernel))
  change (cmpR64R64Effect 0x100657 7 8 s₂).Holds s₂ s₃ at he₃
  have hf₃ : AgreesExcept [.flags, .rip] s₂ s₃ := he₃.agrees
  have code₃ := hf₃.codeIn (by simp [Component.Covers]) code₂
  have hc₄ : CodeIn (codeRange 0x10065a [0x76, 0x0c]) s₃ :=
    init_program_slice code₃ 0x65a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t, step₄, hr₄, he₄⟩ :=
    jcc_rel8_effect_step 0x10065a 6 0x0c s₃ hr₃ hc₄ ⟨he₃.rip, fun _ => by decide +kernel⟩
  have hf₄ : AgreesExcept [.rip] s₃ t := he₄.agrees
  have hlength : s₂.regValue .rdi = BitVec.ofNat 64 (2 * c.input.length) := by
    have hw := he₂.writes
    change s₂.regValue .rdi =
      s₁.regValue .rdx + (s₁.regValue .rdx <<< (0 : Nat)) + 0 at hw
    rw [BitVec.shiftLeft_zero] at hw
    change s₂.regValue .rdi = BitVec.add (BitVec.add (s₁.regValue .rdx) (s₁.regValue .rdx)) 0#64 at hw
    rw [show BitVec.add (BitVec.add (s₁.regValue .rdx) (s₁.regValue .rdx)) 0#64 =
      s₁.regValue .rdx + s₁.regValue .rdx from BitVec.add_zero _] at hw
    have hh : s₁.regValue .rdx = BitVec.ofNat 64 c.input.length :=
      (hf₁.read (n := 64) (r := 2) (by simp)).trans he.length
    rw [hh, ← BitVec.ofNat_add] at hw
    simpa only [Nat.two_mul] using hw
  have hcapacity : s₂.regValue .r8 = BitVec.ofNat 64 c.capacity :=
    (hf₂.read (n := 64) (r := 8) (by simp)).trans
      ((hf₁.read (n := 64) (r := 8) (by simp)).trans he.capacity)
  have hcond : condHolds 6 (StatusFlags.ofRFLAGS s₃.RFLAGS) =
      decide (2 * c.input.length ≤ c.capacity) := by
    change ((StatusFlags.ofRFLAGS s₃.RFLAGS).CF || (StatusFlags.ofRFLAGS s₃.RFLAGS).ZF) = _
    rw [he₃.flags.1, he₃.flags.2.2.2.1, init_cmp_ule]
    change decide (s₂.regValue .rdi ≤ s₂.regValue .r8) = _
    rw [hlength, hcapacity]
    simp only [init_double_input_length_le_capacity]
  have hip : t.RIP = if 2 * c.input.length ≤ c.capacity then 0x100668 else 0x10065c := by
    rw [he₄.rip]
    change (if condHolds 6 (StatusFlags.ofRFLAGS s₃.RFLAGS) then
      (0x100668 : BitVec 64) else 0x10065c) = _
    simp only [hcond, decide_eq_true_eq]
  have ha₄ : Advances (returnBoundary c.initial) 1 s₃ t :=
    Advances.of_step step₄ (.inl (by
      rw [hip]
      split
      · exact hne 0x668 (by decide +kernel)
      · exact hne 0x65c (by decide +kernel)))
  have hframe : AgreesExcept [.reg 0, .reg 7, .flags, .rip] s t :=
    (((hf₁.trans hf₂).trans hf₃).trans hf₄).mono (by simp)
  have hframe₂ : AgreesExcept [.flags, .rip] s₂ t :=
    (hf₃.trans hf₄).mono (by simp)
  have hframe₁ : AgreesExcept [.reg 7, .flags, .rip] s₁ t :=
    ((hf₂.trans hf₃).trans hf₄).mono (by simp)
  have hinv : RunInvariant c t :=
    hs.of_agrees c hr₄ (hframe.mono (by simp [encoderComponents]))
  refine ⟨t, ((ha₁.trans ha₂).trans ha₃).trans ha₄, ?_, hip⟩
  refine ⟨⟨hinv, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (hframe.read (n := 64) (r := 4) (by simp)).trans he.rsp
  · exact (hframe₁.read (n := 64) (r := 0) (by simp)).trans
      ((show s₁.regValue .rax = s.regValue .rdi from he₁.writes).trans he.result)
  · have hm := hframe.external (by simp [Component.Covers])
    change memLoad t.external _ 64 = _
    rw [hm]
    exact he.returnAddress
  · exact (hframe.read (n := 64) (r := 3) (by simp)).trans he.rbx
  · have hm := hframe.external (by simp [Component.Covers])
    change memLoad t.external _ 64 = _
    rw [hm]
    exact he.savedRbx
  · exact (hframe.read (n := 64) (r := 6) (by simp)).trans he.src
  · exact (hframe.read (n := 64) (r := 2) (by simp)).trans he.length
  · exact (hframe.read (n := 64) (r := 1) (by simp)).trans he.dst
  · exact (hframe₂.read (n := 64) (r := 7) (by simp)).trans hlength

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
