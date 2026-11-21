import Sha3.Proofs.Finalize.Layout
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import X86Proofs.Program.Compose
import Sha3.Proofs.Run

namespace Sha3.Proofs.Finalize.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add

def scalarChanges : List Component :=
  [.reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 14, .flags, .rip]

def prefixBytes : List UInt8 :=
  [0xba, 0xc9, 0, 0, 0, 0x48, 0x89, 0xdf, 0x31, 0xf6,
    0x48, 0x83, 0xc4, 8, 0x5b, 0x41, 0x5e]

structure PrefixPre (p ptr sp : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  pointer : (Operand.reg 3 : Operand 64).read s = ptr
  stack : stackPtr s = sp - 24
  readable : ∀ i : Fin 2, MemReadable s (sp - 16 + BitVec.ofNat 64 (8 * i.val)) 8

structure PrefixDone (ptr sp : BitVec 64) (s t : RamState) : Prop where
  pointer : (Operand.reg 7 : Operand 64).read t = ptr
  length : (Operand.reg 2 : Operand 64).read t = 201
  value : (Operand.reg 6 : Operand 64).read t = 0
  stack : stackPtr t = sp
  rbx : (Operand.reg 3 : Operand 64).read t = (Operand.mem (sp - 16) : Operand 64).read s
  r14 : (Operand.reg 14 : Operand 64).read t = (Operand.mem (sp - 8) : Operand 64).read s
  agrees : AgreesExcept scalarChanges s t

theorem scalarChanges_external {s t : RamState}
    (h : AgreesExcept scalarChanges s t) : t.external = s.external :=
  h.external (by simp [scalarChanges, Component.Covers])

private theorem scalarAdvance [Bindings] {boundary : ReturnBoundary}
    {pre : RamState → Prop} {p : BitVec 64} {bytes : List UInt8}
    {effect : RamState → Effect} {code : CodeMap} {model s : RamState} {ws : List Write}
    (step : StepEffect pre (codeRange p bytes) effect)
    (hcode : ∀ x ∈ codeRange p bytes, x ∈ code)
    (full : ∀ w ∈ ws, w.Full) (writes : (effect s).writes = ws)
    (frame : ∀ c ∈ (effect s).components, c ∈ scalarChanges)
    (ready : ReadyToStep s) (loaded : CodeIn code s) (hp : pre s)
    (hne : (effect s).rip ≠ boundary.rip) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      (effect s).Holds s t ∧ Obs (applyWrites model ws) t ∧
      AgreesExcept scalarChanges s t := by
  obtain ⟨t, ht, hr, he⟩ := step.advances ready (loaded.mono hcode) hp hne
  have ha := he.agrees.mono frame
  refine ⟨t, ht, hr, loaded.of_external_eq (scalarChanges_external ha), he, ?_, ha⟩
  rw [← writes]
  exact he.obs obs (by simpa only [writes] using full)

theorem prefix_steps [Bindings] (boundary : ReturnBoundary)
    (p ptr sp : BitVec 64) {code : CodeMap}
    (hcode : ∀ x ∈ codeRange p prefixBytes, x ∈ code)
    (hboundary : ∀ x ∈ [p + 5, p + 8, p + 10, p + 14, p + 15, p + 17],
      x ≠ boundary.rip) :
    AdvanceTriple boundary 6 (PrefixPre p ptr sp) code
      (fun s t ↦ t.RIP = p + (17 : BitVec 64) ∧ PrefixDone ptr sp s t) := by
  intro s hr hc hp
  have hcsub (offset : Nat) (bs : List UInt8)
      (heq : (prefixBytes.drop offset).take bs.length = bs) :
      ∀ x ∈ codeRange (p + BitVec.ofNat 64 offset) bs, x ∈ code := by
    intro x hx
    exact hcode x (codeRange_mem_of_drop offset heq x hx)
  obtain ⟨s1, a1, r1, c1, e1, o1, f1⟩ := scalarAdvance
    (effect := movR32Imm32Effect p 5 2 201) (ws := [⟨(Operand.reg 2 : Operand 64), 201⟩])
    (mov_r32_imm32_effect_step p 0xba (by decide +kernel) 201)
    (by simpa only [BitVec.add_zero] using
      hcsub 0 (0xba :: immBytes 32 201) (by decide +kernel))
    (by simp [Write.Full, Operand.Full]) rfl
    (by simp [movR32Imm32Effect, Effect.components, scalarChanges, Write.component, Operand.component])
    hr hc hp.rip (hboundary (p + 5) (by simp)) (Obs.refl s)
  have hptr := hp.pointer
  x86_norm at hptr
  obtain ⟨s2, a2, r2, c2, e2, o2, f2⟩ := scalarAdvance
    (effect := movR64R64Effect (p + 5) 7 3) (ws := [⟨(Operand.reg 7 : Operand 64), ptr⟩])
    (mov_r64_r64_effect_step (p + 5) 0x48 0xdf
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (hcsub 5 [0x48, 0x89, 0xdf] (by decide +kernel))
    (by simp [Write.Full, Operand.Full])
    (by simp only [movR64R64Effect]; rw [← o1.read (Operand.reg 3 : Operand 64) trivial]; x86_norm; rw [hptr])
    (by simp [movR64R64Effect, Effect.components, scalarChanges, Write.component, Operand.component])
    r1 c1 e1.rip
    (by simpa [movR64R64Effect, BitVec.add_assoc] using hboundary (p + 8) (by simp)) o1
  obtain ⟨s3, a3, r3, c3, e3, o3, f3⟩ := scalarAdvance
    (effect := xorR32R32Effect (p + 8) 2 6 6) (ws := [⟨(Operand.reg 6 : Operand 64), 0⟩])
    (xor_r32_r32_effect_step (p + 8) 0xf6 (by decide +kernel))
    (hcsub 8 [0x31, 0xf6] (by decide +kernel))
    (by simp [Write.Full, Operand.Full]) (by simp [xorR32R32Effect])
    (by simp [xorR32R32Effect, Effect.components, scalarChanges, Write.component, Operand.component])
    r2 c2 (by simpa [movR64R64Effect, BitVec.add_assoc] using e2.rip)
    (by simpa [xorR32R32Effect, BitVec.add_assoc] using hboundary (p + 10) (by simp)) o2
  have hs : (Operand.reg 4 : Operand 64).read s = sp - 24 := hp.stack
  have hsadd : (sp - 24) + (8 : BitVec 64) = sp - 16 := by
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  x86_norm at hs hsadd
  obtain ⟨s4, a4, r4, c4, e4, o4, f4⟩ := scalarAdvance
    (effect := addR64Imm8Effect (p + 10) 4 8)
    (ws := [⟨(Operand.reg 4 : Operand 64), sp - 16⟩])
    (add_r64_imm8_effect_step (p + 10) 0x48 0xc4 8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (hcsub 10 [0x48, 0x83, 0xc4, 8] (by decide +kernel))
    (by simp [Write.Full, Operand.Full])
    (by simp only [addR64Imm8Effect]; rw [← o3.read (Operand.reg 4 : Operand 64) trivial]; x86_norm; rw [hs, hsadd])
    (by simp [addR64Imm8Effect, Effect.components, scalarChanges, Write.component, Operand.component])
    r3 c3 (by simpa [xorR32R32Effect, BitVec.add_assoc] using e3.rip)
    (by simpa [addR64Imm8Effect, BitVec.add_assoc] using hboundary (p + 14) (by simp)) o3
  have f04 : AgreesExcept scalarChanges s s4 :=
    (f1.trans (f2.trans (f3.trans f4))).mono (by
      intro c hc; simpa only [List.mem_append, or_self] using hc)
  have m4 := scalarChanges_external f04
  have sp4 : stackPtr s4 = sp - 16 := by
    change (Operand.reg 4 : Operand 64).read s4 = _
    rw [← o4.read (Operand.reg 4 : Operand 64) trivial]; x86_norm
  have rd4 : MemReadable s4 (stackPtr s4) 8 := by
    rw [sp4]
    simpa using (hp.readable ⟨0, by decide⟩).of_external_eq m4
  obtain ⟨s5, a5, r5, c5, e5, o5, f5⟩ := scalarAdvance
    (effect := popR64Effect (p + 14) 1 3)
    (ws := [⟨(Operand.reg 3 : Operand 64), (Operand.mem (sp - 16) : Operand 64).read s⟩,
      ⟨(Operand.reg 4 : Operand 64), sp - 8⟩])
    (pop_r64_effect_step (p + 14) 0x5b (by decide +kernel) (by decide +kernel))
    (hcsub 14 [0x5b] (by decide +kernel))
    (by simp [Write.Full, Operand.Full])
    (by simp [popR64Effect, sp4, Operand.read, m4, BitVec.sub_eq_add_neg, BitVec.add_assoc])
    (by simp [popR64Effect, Effect.components, scalarChanges, Write.component, Operand.component])
    r4 c4 ⟨by simpa [addR64Imm8Effect, BitVec.add_assoc] using e4.rip, rd4⟩
    (by simpa [popR64Effect, BitVec.add_assoc] using hboundary (p + 15) (by simp)) o4
  have f05 := (f04.trans f5).mono (by
    intro c hc; simpa only [List.mem_append, or_self] using hc)
  have m5 := scalarChanges_external f05
  have sp5 : stackPtr s5 = sp - 8 := by
    have h : stackPtr s5 = stackPtr s4 + 8 := e5.writes.2
    simpa [sp4, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
  have rd5 : MemReadable s5 (stackPtr s5) 8 := by
    rw [sp5]
    simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using
      (hp.readable ⟨1, by decide⟩).of_external_eq m5
  obtain ⟨s6, a6, r6, c6, e6, o6, f6⟩ := scalarAdvance
    (effect := popR64Effect (p + 15) 2 14)
    (ws := [⟨(Operand.reg 14 : Operand 64), (Operand.mem (sp - 8) : Operand 64).read s⟩,
      ⟨(Operand.reg 4 : Operand 64), sp⟩])
    (pop_r64_rex_effect_step (p + 15) 0x41 0x5e
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (hcsub 15 [0x41, 0x5e] (by decide +kernel))
    (by simp [Write.Full, Operand.Full])
    (by simp [popR64Effect, sp5, Operand.read, m5, BitVec.sub_add_cancel])
    (by simp [popR64Effect, Effect.components, scalarChanges, Write.component, Operand.component])
    r5 c5 ⟨by simpa [popR64Effect, BitVec.add_assoc] using e5.rip, rd5⟩
    (by simpa [popR64Effect, BitVec.add_assoc] using hboundary (p + 17) (by simp)) o5
  refine ⟨s6, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6)))), r6, c6,
    by simpa [popR64Effect, BitVec.add_assoc] using e6.rip, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← o6.read (Operand.reg 7 : Operand 64) trivial]; x86_norm
  · rw [← o6.read (Operand.reg 2 : Operand 64) trivial]; x86_norm
  · rw [← o6.read (Operand.reg 6 : Operand 64) trivial]; x86_norm
  · change (Operand.reg 4 : Operand 64).read s6 = sp
    rw [← o6.read (Operand.reg 4 : Operand 64) trivial]; x86_norm
  · rw [← o6.read (Operand.reg 3 : Operand 64) trivial]; x86_norm
  · rw [← o6.read (Operand.reg 14 : Operand 64) trivial]; x86_norm
  · exact (f05.trans f6).mono (by
      intro c hc; simpa only [List.mem_append, or_self] using hc)

end Sha3.Proofs.Finalize.Reset
