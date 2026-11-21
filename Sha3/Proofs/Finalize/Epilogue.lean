import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple
import Sha3.Proofs.Run
import Sha3.Proofs.Finalize.Layout
import Sha3.Proofs.Image

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def epilogueChanges : List Component := [.reg 3, .reg 14, .reg 4, .flags, .rip]

def finalizeEpilogueBytes : List UInt8 := [0x48, 0x83, 0xc4, 8, 0x5b, 0x41, 0x5e, 0xc3]

def finalizeEpilogueCode (p : BitVec 64) : CodeMap := codeRange p finalizeEpilogueBytes

structure FinalizeEpiloguePre (p q sp : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  stack : stackPtr s = sp - 32
  readable : ∀ i : Fin 3, MemReadable s (sp - 24 + BitVec.ofNat 64 (8 * i.val)) 8
  returnSlot : (Operand.mem (sp - 8) : Operand 64).read s = q
  target : q.toNat < 2^32

structure FinalizeEpilogueResult (q sp : BitVec 64) (start final : RamState) : Prop where
  rip : final.RIP = q
  stack : stackPtr final = sp
  memory : final.external = start.external
  agrees : AgreesExcept epilogueChanges start final
  rbx : (Operand.reg 3 : Operand 64).read final =
    (Operand.mem (sp - 24) : Operand 64).read start
  r14 : (Operand.reg 14 : Operand 64).read final =
    (Operand.mem (sp - 16) : Operand 64).read start

theorem epilogueChanges_external {s t : RamState}
    (h : AgreesExcept epilogueChanges s t) : t.external = s.external := by
  exact h.external (by
    simp only [epilogueChanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl | rfl) x <;> exact id)

theorem epilogueChanges_trans {s t u : RamState}
    (h : AgreesExcept epilogueChanges s t) (h' : AgreesExcept epilogueChanges t u) :
    AgreesExcept epilogueChanges s u :=
  (h.trans h').mono (fun _ hc ↦ (List.mem_append.mp hc).elim id id)

def finalizeEpiloguePrefixBytes : List UInt8 := [0x48, 0x83, 0xc4, 8, 0x5b, 0x41, 0x5e]

structure FinalizeEpiloguePrefixPre (p sp : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  stack : stackPtr s = sp - 32
  readable : ∀ i : Fin 2, MemReadable s (sp - 24 + BitVec.ofNat 64 (8 * i.val)) 8

structure FinalizeEpiloguePrefixResult (p sp : BitVec 64) (start final : RamState) : Prop where
  rip : final.RIP = p + (7 : BitVec 64)
  stack : stackPtr final = sp - 8
  memory : final.external = start.external
  agrees : AgreesExcept epilogueChanges start final
  rbx : (Operand.reg 3 : Operand 64).read final =
    (Operand.mem (sp - 24) : Operand 64).read start
  r14 : (Operand.reg 14 : Operand 64).read final =
    (Operand.mem (sp - 16) : Operand 64).read start

theorem finalizeEpiloguePrefix_advance [Bindings] (boundary : ReturnBoundary)
    (p sp : BitVec 64) {code : CodeMap}
    (hcode : ∀ x ∈ codeRange p finalizeEpiloguePrefixBytes, x ∈ code)
    (hboundary : ∀ x ∈ [p + 4, p + 5, p + 7], x ≠ boundary.rip) :
    AdvanceTriple boundary 3 (FinalizeEpiloguePrefixPre p sp) code
      (fun s t ↦ FinalizeEpiloguePrefixResult p sp s t) := by
  intro s hready hc hp
  have hc0 : ∀ x ∈ codeRange p [0x48, 0x83, 0xc4, 8], x ∈ code := by
    intro x hx
    apply hcode x
    exact codeRange_mem_of_drop (p := p) (all := finalizeEpiloguePrefixBytes)
      (bytes := [0x48, 0x83, 0xc4, 8]) 0 (by decide +kernel) x
      (by simpa only [BitVec.add_zero] using hx)
  have hc1 : ∀ x ∈ codeRange (p + 4) [0x5b], x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop (p := p) (all := finalizeEpiloguePrefixBytes) 4
      (by decide +kernel) x hx)
  have hc2 : ∀ x ∈ codeRange (p + 5) [0x41, 0x5e], x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop (p := p) (all := finalizeEpiloguePrefixBytes) 5
      (by decide +kernel) x hx)
  have hadd := add_r64_imm8_effect_step p 0x48 0xc4 8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨s₁, hr₁, ht₁, he₁⟩ := hadd.advances hready (hc.mono hc0) hp.rip
    (hboundary (p + 4) (by simp))
  have ha₁ : AgreesExcept epilogueChanges s s₁ := he₁.agrees.mono (by
    change ∀ c ∈ [Component.reg 4, .flags, .rip], c ∈ epilogueChanges
    simp [epilogueChanges])
  have hm₁ := epilogueChanges_external ha₁
  have hs₁ : stackPtr s₁ = sp - 24 := by
    have h := he₁.writes
    change stackPtr s₁ = stackPtr s + 8 at h
    rw [h, hp.stack]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have hread₁ : MemReadable s₁ (stackPtr s₁) 8 := by
    rw [hs₁]
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (hp.readable ⟨0, by decide⟩).of_external_eq hm₁
  have hc₁ := he₁.codeIn (addR64Imm8Effect_avoids _ _ _ _ _) hc
  have hpop₁ := pop_r64_effect_step (p + 4) 0x5b (by decide +kernel) (by decide +kernel)
  obtain ⟨s₂, hr₂, ht₂, he₂⟩ :=
    hpop₁.advances ht₁ (hc₁.mono hc1) ⟨he₁.rip, hread₁⟩
    (by simpa only [popR64Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
      hboundary (p + 5) (by simp))
  have ha₂ : AgreesExcept epilogueChanges s₁ s₂ := he₂.agrees.mono (by
    change ∀ c ∈ [Component.reg 3, .reg 4, .rip], c ∈ epilogueChanges
    simp [epilogueChanges])
  have hm₂ := (epilogueChanges_external ha₂).trans hm₁
  have hs₂ : stackPtr s₂ = sp - 16 := by
    have h : stackPtr s₂ = stackPtr s₁ + 8 := he₂.writes.2
    rw [h, hs₁]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have hread₂ : MemReadable s₂ (stackPtr s₂) 8 := by
    rw [hs₂]
    have h := (hp.readable ⟨1, by decide⟩).of_external_eq hm₂
    simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
  have hc₂ := he₂.codeIn (popR64Effect_avoids _ _ _ _ _) hc₁
  have hpop₂ := pop_r64_rex_effect_step (p + 5) 0x41 0x5e
    (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨s₃, hr₃, ht₃, he₃⟩ := hpop₂.advances ht₂ (hc₂.mono hc2)
    ⟨by simpa only [popR64Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
        he₂.rip, hread₂⟩
    (by simpa only [popR64Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
      hboundary (p + 7) (by simp))
  have ha₃ : AgreesExcept epilogueChanges s₂ s₃ := he₃.agrees.mono (by
    change ∀ c ∈ [Component.reg 14, .reg 4, .rip], c ∈ epilogueChanges
    simp [epilogueChanges])
  have hm₃ := (epilogueChanges_external ha₃).trans hm₂
  have hs₃ : stackPtr s₃ = sp - 8 := by
    have h : stackPtr s₃ = stackPtr s₂ + 8 := he₃.writes.2
    rw [h, hs₂]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have hbx₂ : (Operand.reg 3 : Operand 64).read s₂ =
      (Operand.mem (sp - 24) : Operand 64).read s := by
    have h := he₂.writes.1
    change (Operand.reg 3 : Operand 64).read s₂ =
      (Operand.mem (stackPtr s₁) : Operand 64).read s₁ at h
    simpa only [Operand.read, hs₁, hm₁] using h
  have h14₃ : (Operand.reg 14 : Operand 64).read s₃ =
      (Operand.mem (sp - 16) : Operand 64).read s := by
    have h := he₃.writes.1
    change (Operand.reg 14 : Operand 64).read s₃ =
      (Operand.mem (stackPtr s₂) : Operand 64).read s₂ at h
    simpa only [Operand.read, hs₂, hm₂] using h
  have hbx₃ := he₃.agrees.read (n := 64) (r := 3) (by
    change Component.reg 3 ∉ [Component.reg 14, .reg 4, .rip]
    decide +kernel)
  have hag := epilogueChanges_trans (epilogueChanges_trans ha₁ ha₂) ha₃
  refine ⟨s₃, (hr₁.trans hr₂).trans hr₃, ht₃, hc.of_external_eq hm₃, ?_, hs₃,
    hm₃, hag, hbx₃.trans hbx₂, h14₃⟩
  simpa only [popR64Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
    BitVec.reduceAdd] using he₃.rip

theorem finalizeEpilogue_advance [Bindings] (boundary : ReturnBoundary)
    (p q sp : BitVec 64) {code : CodeMap}
    (hcode : ∀ x ∈ finalizeEpilogueCode p, x ∈ code)
    (hboundary : ∀ x ∈ [p + 4, p + 5, p + 7, q], x ≠ boundary.rip) :
    AdvanceTriple boundary 4 (FinalizeEpiloguePre p q sp) code
      (fun s t ↦ FinalizeEpilogueResult q sp s t) := by
  intro s hready hc hp
  have hprefix : ∀ x ∈ codeRange p finalizeEpiloguePrefixBytes, x ∈ code := by
    intro x hx
    apply hcode x
    exact codeRange_mem_of_take (all := finalizeEpilogueBytes) (by decide +kernel) x hx
  have hb : ∀ x ∈ [p + 4, p + 5, p + 7], x ≠ boundary.rip := by
    intro x hx
    apply hboundary x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨a, hrun, hreadyA, hcodeA, ha⟩ :=
    finalizeEpiloguePrefix_advance boundary p sp hprefix hb s hready hc
      ⟨hp.rip, hp.stack, fun i ↦ hp.readable ⟨i.val, by omega⟩⟩
  have hret : ∀ x ∈ codeRange (p + 7) [0xc3], x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop (p := p) (all := finalizeEpilogueBytes) 7
      (by decide +kernel) x hx)
  have hread : MemReadable a (stackPtr a) 8 := by
    rw [ha.stack]
    have h := (hp.readable ⟨2, by decide⟩).of_external_eq ha.memory
    simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
  have htop : stackTop a = q := by
    change memLoad a.external (stackPtr a) 64 = q
    rw [ha.stack, ha.memory]
    exact hp.returnSlot
  obtain ⟨t, hretRun, ht, he⟩ := (ret_effect_step (p + 7)).advances hreadyA
    (hcodeA.mono hret) ⟨⟨ha.rip, hread⟩, htop ▸ hp.target⟩
    (by change stackTop a ≠ boundary.rip; rw [htop]; exact hboundary q (by simp))
  have hag : AgreesExcept epilogueChanges a t := he.agrees.mono (by
    simp [retEffect_components, epilogueChanges])
  have hall := epilogueChanges_trans ha.agrees hag
  have hbx := he.agrees.read (n := 64) (r := 3) (by
    change Component.reg 3 ∉ [Component.reg 4, .rip]
    decide +kernel)
  have h14 := he.agrees.read (n := 64) (r := 14) (by
    change Component.reg 14 ∉ [Component.reg 4, .rip]
    decide +kernel)
  refine ⟨t, hrun.trans hretRun, ht, hc.of_external_eq (epilogueChanges_external hall),
    he.rip.trans htop, ?_, epilogueChanges_external hall, hall,
    hbx.trans ha.rbx, h14.trans ha.r14⟩
  exact he.writes.trans ((congrArg (· + 8) ha.stack).trans (BitVec.sub_add_cancel _ _))

theorem finalizeEpilogue_image (v : Variant) (keccak : Bool := false) :
    ∀ x ∈ finalizeEpilogueCode (epilogueAddress v false (keccak := keccak)), x ∈
        Extracted.programImage := by
  have h :
      let p := epilogueAddress v false (keccak := keccak)
      let offset := p.toNat - Extracted.textAddress.toNat
      p = Extracted.textAddress + BitVec.ofNat 64 offset ∧
        offset + finalizeEpilogueBytes.length ≤ Extracted.textBytes.size ∧
        Extracted.textBytes.toListFrom offset finalizeEpilogueBytes.length =
          finalizeEpilogueBytes := by
    cases v <;> cases keccak <;> decide +kernel
  obtain ⟨hp, hbound, hslice⟩ := h
  unfold finalizeEpilogueCode
  rw [hp]
  exact textSlice_subset_programImage hbound hslice

theorem finalizeEpilogue_inProgram (v : Variant) (offset : Fin 8) (keccak : Bool := false) :
    InProgram (epilogueAddress v false (keccak := keccak) + BitVec.ofNat 64 offset.val) :=
  ⟨finalizeEpilogueBytes[offset.val], finalizeEpilogue_image (keccak := keccak) v _
    (mem_codeRange _ finalizeEpilogueBytes offset.val offset.isLt)⟩

end Sha3.Proofs.Finalize
