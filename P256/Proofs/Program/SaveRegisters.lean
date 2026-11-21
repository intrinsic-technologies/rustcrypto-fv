import P256.Proofs.Program.PushSequence
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false


namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r13, 32), (.r12, 40), (.rbx, 48)]

def saveMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore s.external
    (stackPtr s - 8) (s.regValue .rbp))
    (stackPtr s - 16) (s.regValue .r15))
    (stackPtr s - 24) (s.regValue .r14))
    (stackPtr s - 32) (s.regValue .r13))
    (stackPtr s - 40) (s.regValue .r12))
    (stackPtr s - 48) (s.regValue .rbx)

def saveFrame (s : RamState) : List Component :=
  [.reg 4, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .mem (stackPtr s - 24) 8, .mem (stackPtr s - 32) 8,
    .mem (stackPtr s - 40) 8, .mem (stackPtr s - 48) 8]

structure SaveCode (offset : Nat) : Prop where
  bounded : offset + 10 < 118431
  rbp : Extracted.textBytes.toListFrom offset 1 = [0x55]
  r15 : Extracted.textBytes.toListFrom (offset + 1) 2 = [0x41, 0x57]
  r14 : Extracted.textBytes.toListFrom (offset + 3) 2 = [0x41, 0x56]
  r13 : Extracted.textBytes.toListFrom (offset + 5) 2 = [0x41, 0x55]
  r12 : Extracted.textBytes.toListFrom (offset + 7) 2 = [0x41, 0x54]
  rbx : Extracted.textBytes.toListFrom (offset + 9) 1 = [0x53]

theorem save_registers [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {reserve codeOffset : Nat}
    (hStack : Stack.Valid s reserve)
    (hAvoid : (Stack.region s reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (hOuter : ¬ InProgram boundary.rip)
    (hReady : ReadyToStep s) (hLoaded : ProgramLoaded s)
    (hreserve : 48 ≤ reserve)
    (hRip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (code : SaveCode codeOffset) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 10) ∧ stackPtr t = stackPtr s - 48 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s) s t := by
  have bytes : PushSequenceCode codeOffset [5,15,14,13,12,3] := by
    simp only [PushSequenceCode,
      show encodePushR64 5 = [0x55] from rfl,
      show encodePushR64 15 = [0x41,0x57] from rfl,
      show encodePushR64 14 = [0x41,0x56] from rfl,
      show encodePushR64 13 = [0x41,0x55] from rfl,
      show encodePushR64 12 = [0x41,0x54] from rfl,
      show encodePushR64 3 = [0x53] from rfl,
      List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd]
    exact ⟨by have h := code.bounded; omega, code.rbp,
      by have h := code.bounded; omega, code.r15,
      by have h := code.bounded; omega, code.r14,
      by have h := code.bounded; omega, code.r13,
      by have h := code.bounded; omega, code.r12,
      code.bounded, code.rbx, True.intro⟩
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) [5,15,14,13,12,3] hStack hAvoid hOuter
      hReady hLoaded (fun _ h => h) (by simp) hRip hreserve (by decide)
      (by decide) (fun _ _ => rfl) bytes
  refine ⟨t, run, ready, loaded, rip, rsp, memory, agrees.mono ?_⟩
  intro c hc
  simp only [pushSequenceFrame, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
    (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals simp [saveFrame]

theorem saveMemory_saved (s : RamState) (entry : Syntax.Reg × Nat)
    (hentry : entry ∈ savedRegisters) :
    memLoad (saveMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 =
      s.regValue entry.1 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

end P256.Proofs.Program
