import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Nop.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

structure MixedProloguePre (s : RamState) : Prop where
  rip : s.RIP = 0x1001e7
  write8 : MemWritable s (stackPtr s - 8) 8
  write16 : MemWritable s (stackPtr s - 16) 8
  write24 : MemWritable s (stackPtr s - 24) 8
  avoid : ∀ i < 24, ¬ InProgram (stackPtr s - 24 + BitVec.ofNat 64 i)

def mixedPrologueEffect (s : RamState) : Effect where
  rip := 0x1001f0
  writes := [⟨(.reg 4 : Operand 64), stackPtr s - 24⟩,
    ⟨(.mem (stackPtr s - 8) : Operand 64), s.regValue .rbp⟩,
    ⟨(.mem (stackPtr s - 16) : Operand 64), s.regValue .r14⟩,
    ⟨(.mem (stackPtr s - 24) : Operand 64), s.regValue .rbx⟩,
    ⟨(.reg 6 : Operand 64), 0⟩, ⟨(.reg 0 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read pushAddr pushEffect BitVec.sub_eq_add_neg

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem mixed_loop_prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hPre : MixedProloguePre s) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (mixedPrologueEffect s).Holds s t := by
  have avoid (back : Nat) (hb : back ≤ 24) (hb8 : 8 ≤ back) :
      ∀ i < 8, ¬ InProgram (stackPtr s - BitVec.ofNat 64 back + BitVec.ofNat 64 i) := by
    intro i hi hp
    apply hPre.avoid (24 - back + i) (by omega)
    have he : stackPtr s - 24 + BitVec.ofNat 64 (24 - back + i) =
        stackPtr s - BitVec.ofNat 64 back + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc,
        ← BitVec.ofNat_sub_ofNat_of_le 24 back (by omega) hb]
      simp only [BitVec.ofNat_eq_ofNat]
      rw [BitVec.sub_eq_add_neg (24#64), ← BitVec.add_assoc,
        BitVec.sub_add_cancel, ← BitVec.sub_eq_add_neg]
    rwa [he]
  have addra : pushAddr s = stackPtr s - 8 := by
    rfl
  have prea : PushPre 0x1001e7 1 s := by
    refine ⟨hPre.rip, ?_, ?_⟩
    · rw [addra]
      exact hPre.write8
    · rw [addra]
      intro i hi j hj he
      apply avoid 8 (by decide) (by decide) i hi
      change InProgram (stackPtr s - _ + BitVec.ofNat 64 i)
      exact he.symm ▸ (by
        have hp := text_address_in_program (487 + j) (by
          have : Extracted.textBytes.size > 488 := by decide +kernel
          omega)
        simpa only [BitVec.ofNat_add, Extracted.textAddress, ← BitVec.add_assoc,
          BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hp)
  obtain ⟨a, runa, readya, effecta⟩ :=
    (push_r64_effect_step 0x1001e7 0x55 (by decide)).advances
      hReady (program_text_slice hCode 0x1e7 1 (by decide +kernel)) prea
      (outsideMixed_ne (pc := 0x1001e8) hOutside (by decide) (by decide))
  change (pushR64Effect 0x1001e7 1 5 s).Holds s a at effecta
  have framea : AgreesExcept [.reg 4, .mem (stackPtr s - 8) 8, .rip] s a := by
    simpa only [pushR64Effect_components, addra] using effecta.agrees
  have rspa : stackPtr a = stackPtr s - 8 := by
    exact effecta.writes.1.trans addra
  have codea : CodeIn Extracted.programImage a := by
    refine CodeIn.of_agreesExcept framea ?_ hCode
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i, hi, he⟩ := hcov
    exact avoid 8 (by decide) (by decide) i hi (he ▸ ⟨x.2, hx⟩)
  have frameAlla := framea
  have addrb : pushAddr a = stackPtr s - 16 := by
    change stackPtr a - 8 = _
    rw [show stackPtr a = stackPtr s - 8 from rspa]
    simp only [BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have preb : PushPre 0x1001e8 2 a := by
    refine ⟨effecta.rip, ?_, ?_⟩
    · rw [addrb]
      exact ⟨hPre.write16.low,
        fun i hi => frameAlla.grow _ (hPre.write16.mem i hi), hPre.write16.tables⟩
    · rw [addrb]
      intro i hi j hj he
      apply avoid 16 (by decide) (by decide) i hi
      change InProgram (stackPtr s - _ + BitVec.ofNat 64 i)
      exact he.symm ▸ (by
        have hp := text_address_in_program (488 + j) (by
          have : Extracted.textBytes.size > 490 := by decide +kernel
          omega)
        simpa only [BitVec.ofNat_add, Extracted.textAddress, ← BitVec.add_assoc,
          BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hp)
  obtain ⟨b, runb, readyb, effectb⟩ :=
    (push_r64_rex_effect_step 0x1001e8 0x41 0x56 (by unfold RexPrefix; decide) (by decide)).advances
      readya (program_text_slice codea 0x1e8 2 (by decide +kernel)) preb
      (outsideMixed_ne (pc := 0x1001ea) hOutside (by decide) (by decide))
  change (pushR64Effect 0x1001e8 2 14 a).Holds a b at effectb
  have frameb : AgreesExcept [.reg 4, .mem (stackPtr s - 16) 8, .rip] a b := by
    simpa only [pushR64Effect_components, addrb] using effectb.agrees
  have rspb : stackPtr b = stackPtr s - 16 := by
    exact effectb.writes.1.trans addrb
  have codeb : CodeIn Extracted.programImage b := by
    refine CodeIn.of_agreesExcept frameb ?_ codea
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i, hi, he⟩ := hcov
    exact avoid 16 (by decide) (by decide) i hi (he ▸ ⟨x.2, hx⟩)
  have frameAllb := frameAlla.trans frameb
  have addrc : pushAddr b = stackPtr s - 24 := by
    change stackPtr b - 8 = _
    rw [show stackPtr b = stackPtr s - 16 from rspb]
    simp only [BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have prec : PushPre 0x1001ea 1 b := by
    refine ⟨effectb.rip, ?_, ?_⟩
    · rw [addrc]
      exact ⟨hPre.write24.low,
        fun i hi => frameAllb.grow _ (hPre.write24.mem i hi), hPre.write24.tables⟩
    · rw [addrc]
      intro i hi j hj he
      apply avoid 24 (by decide) (by decide) i hi
      change InProgram (stackPtr s - _ + BitVec.ofNat 64 i)
      exact he.symm ▸ (by
        have hp := text_address_in_program (490 + j) (by
          have : Extracted.textBytes.size > 491 := by decide +kernel
          omega)
        simpa only [BitVec.ofNat_add, Extracted.textAddress, ← BitVec.add_assoc,
          BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hp)
  obtain ⟨c, runc, readyc, effectc⟩ :=
    (push_r64_effect_step 0x1001ea 0x53 (by decide)).advances
      readyb (program_text_slice codeb 0x1ea 1 (by decide +kernel)) prec
      (outsideMixed_ne (pc := 0x1001eb) hOutside (by decide) (by decide))
  change (pushR64Effect 0x1001ea 1 3 b).Holds b c at effectc
  have framec : AgreesExcept [.reg 4, .mem (stackPtr s - 24) 8, .rip] b c := by
    simpa only [pushR64Effect_components, addrc] using effectc.agrees
  have codec : CodeIn Extracted.programImage c := by
    refine CodeIn.of_agreesExcept framec ?_ codeb
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i, hi, he⟩ := hcov
    exact avoid 24 (by decide) (by decide) i hi (he ▸ ⟨x.2, hx⟩)
  obtain ⟨d, rund, readyd, effectd⟩ :=
    (xor_r32_r32_effect_step 0x1001eb 0xf6 (by decide)).advances
      readyc (program_text_slice codec 0x1eb 2 (by decide +kernel)) effectc.rip
      (outsideMixed_ne (pc := 0x1001ed) hOutside (by decide) (by decide))
  change (xorR32R32Effect 0x1001eb 2 6 6 c).Holds c d at effectd
  have framed : AgreesExcept [.reg 6, .flags, .rip] c d := effectd.agrees
  have coded := framed.codeIn (by simp [Component.Covers]) codec
  obtain ⟨e, rune, readye, effecte⟩ :=
    (xor_r32_r32_effect_step 0x1001ed 0xc0 (by decide)).advances
      readyd (program_text_slice coded 0x1ed 2 (by decide +kernel)) effectd.rip
      (outsideMixed_ne (pc := 0x1001ef) hOutside (by decide) (by decide))
  change (xorR32R32Effect 0x1001ed 2 0 0 d).Holds d e at effecte
  have framee : AgreesExcept [.reg 0, .flags, .rip] d e := effecte.agrees
  have codee := framee.codeIn (by simp [Component.Covers]) coded
  obtain ⟨t, runt, readyt, effectt⟩ :=
    (nop_effect_step 0x1001ef).advances
      readye (program_text_slice codee 0x1ef 1 (by decide +kernel)) effecte.rip
      (outsideMixed_ne (pc := 0x1001f0) hOutside (by decide) (by decide))
  change (nopEffect 0x1001ef 1).Holds e t at effectt
  have framet : AgreesExcept [.rip] e t := effectt.agrees
  have codet := framet.codeIn (by simp [Component.Covers]) codee
  have hab := effecta.seq (by x86_local) (by x86_norm) effectb
  have habc := hab.seq (by x86_local) (by x86_norm) effectc
  have habcd := habc.seq (by x86_local) (by x86_norm) effectd
  have habcde := habcd.seq (by x86_local) (by x86_norm) effecte
  have hall := habcde.seq (e₂ := fun _ => nopEffect 0x1001ef 1) (by x86_local) (by x86_norm) effectt
  refine ⟨t, ((((runa.trans runb).trans runc).trans rund).trans rune).trans runt,
    readyt, codet, ?_⟩
  apply hall.weaken
  · x86_norm [mixedPrologueEffect]
  · x86_norm [mixedPrologueEffect, BitVec.xor_self, BitVec.setWidth_zero]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [mixedPrologueEffect]
  · x86_norm [mixedPrologueEffect]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
