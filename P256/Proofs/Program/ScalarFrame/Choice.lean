import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.SecretKeyFromBytes.Choice
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes (ChoicePre choice_code_loaded choice_correct)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def choiceClobbers (s : RamState) (frameOffset : Nat) : List Component :=
  [.reg 0, .reg 4, .flags, .rip,
    .mem (stackPtr s - BitVec.ofNat 64 (frameOffset + 8)) 8, .mem (stackPtr s - BitVec.ofNat 64 (frameOffset + 9)) 1]

theorem choice_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes stackReserve frameOffset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve)
    (hframe : frameOffset + 9 ≤ stackReserve) (halign : (frameOffset + 8) % 8 = 0)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 frameOffset)
    (offset : Nat) (disp : BitVec 32) (bound : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 6 t u ∧ ReadyToStep u ∧ stackPtr u = stackPtr t ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + 5#64 ∧
      u.regValue .rax = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (choiceClobbers s frameOffset) t u := by
  let p := Extracted.textAddress + BitVec.ofNat 64 offset
  have hp : pushAddr t = stackPtr s - BitVec.ofNat 64 (frameOffset + 8) := by simp only [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]; rfl
  obtain ⟨v, hv, rv, ev⟩ := call_step pre (frameOffset := frameOffset) (by omega) halign ready loaded allocated rsp offset disp
    (by omega) bytes (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0x19070 (by decide)) rip
  have ev' : (callEffect (fun _ => 0x119070) (p + 5#64) t).Holds t v := by
    change (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64)) (p + 5#64) t).Holds t v at ev
    rw [target] at ev
    exact ev
  have spv : stackPtr v = stackPtr s - BitVec.ofNat 64 (frameOffset + 8) := ev'.writes.1.trans hp
  have topv : stackTop v = p + 5#64 := (callEffect_stack ev').1
  have fv : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 (frameOffset + 8)) 8, .rip] t v := by
    simpa only [pushEffect_components, hp] using ev'.agrees
  have callFrame : MemoryWriteFrame t v #v[Stack.region s stackReserve] := by
    apply ev'.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [hp] at ha
    exact ⟨Stack.region s stackReserve, by simp, stack_contains pre (by omega) (by omega) ha⟩
  have loadedv : ProgramLoaded v := by
    intro a b hb
    rw [callFrame a]
    · exact loaded a b hb
    · intro region hr ha
      have he : region = Stack.region s stackReserve := by simpa using hr
      subst region
      exact pre.avoids _ (by simp) a ha (.inl ⟨b,hb⟩)
  have allocatedv := fun a ha => ev'.agrees.grow a (allocated a ha)
  have subOne : BitVec.ofNat 64 (frameOffset+8) + 1 = BitVec.ofNat 64 (frameOffset+9) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have chip : InProgram (p + 5#64) := by
    have h := inProgram_of_textOffset (offset + 5) bound
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, p] using h
  have cp : ChoicePre v := by
    refine ⟨ev'.rip, ?_, ?_, ?_, ?_⟩
    · rw [spv, BitVec.sub_sub, subOne]
      exact P256.Proofs.Program.writable_of_grow
        (P256.Proofs.Program.stack_sub_writable pre.stack
          (fun a ha hpt => pre.avoids _ (by simp) a ha (.inr hpt)) (offset := frameOffset+9) (len := 1) (by omega) (by omega)
          (by decide) (by have h := Nat.mod_lt (stackPtr s - BitVec.ofNat 64 (frameOffset + 9)).toNat (by decide : 0 < 4096); omega)) allocatedv
    · rw [spv]
      exact P256.Proofs.Program.readable_of_grow
        (P256.Proofs.Program.stack_sub_readable pre.stack (by omega) (by omega)) allocatedv
    · rw [topv]
      exact P256.Proofs.Program.inProgram_low chip
    · rw [spv, BitVec.sub_sub, subOne]
      intro i hi j hj he
      apply pre.avoids (Stack.region s stackReserve) (by simp) _
        (stack_contains pre (offset := frameOffset+9) (len := 1) (by omega) (by omega) ⟨i, hi, rfl⟩)
      left
      change stackPtr s - BitVec.ofNat 64 (frameOffset + 9) + BitVec.ofNat 64 i = _ at he
      rw [he]
      have h := inProgram_of_textOffset (0x19070 + j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h

  obtain ⟨u, hu, ru, eu⟩ := choice_correct rv (choice_code_loaded loadedv) cp (by
    intro q hq
    apply boundary_ne_program pre.outerBoundary
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact inProgram_of_textOffset 0x19074 (by decide)
    · exact inProgram_of_textOffset 0x19078 (by decide)
    · exact inProgram_of_textOffset 0x1907c (by decide)
    · exact inProgram_of_textOffset 0x19080 (by decide)
    · rw [topv]; exact chip)
  have fu : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - BitVec.ofNat 64 (frameOffset + 9)) 1] v u := by
    simpa only [spv, BitVec.sub_sub, subOne] using eu.agrees
  have f : AgreesExcept (choiceClobbers s frameOffset) t u := (fv.trans fu).mono (by simp [choiceClobbers])
  have spu : stackPtr u = stackPtr t := eu.rsp.trans (callEffect_stack ev').2
  refine ⟨u, hv.trans hu, ru, spu, eu.rip.trans topv, ?_, f⟩
  change (Operand.reg 0 : Operand 64).read u = _
  rw [eu.rax, fv.read (by simp)]

end P256.Proofs.Program.ScalarFrame
