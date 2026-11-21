import P256.Proofs.Program.Compare.Frame.Save
import P256.Proofs.Program.Compare.Frame.Setup
import P256.Proofs.Program.Compare.Stack
import P256.Proofs.Program.Compare.Model

namespace P256.Proofs.Program.Compare.Frame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program.Compare.Block
open P256.Spec.Program P256.Spec.Program.Routines

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

private theorem component_mem_beq_reg (a : BitVec 64) (n : Nat) (r : BitVec 5) :
    (Component.mem a n == Component.reg r) = false := rfl

private theorem component_reg_beq_mem (r : BitVec 5) (a : BitVec 64) (n : Nat) :
    (Component.reg r == Component.mem a n) = false := rfl

attribute [local x86_compose] component_mem_beq_reg component_reg_beq_mem stackPtr_read
  BitVec.sub_eq_add_neg BitVec.add_assoc

private theorem setup_local : Effect.Local setupEffect := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro s t h
    simp only [setupEffect, h.read_reg]
  · intro s t h i hi
    simp only [Effect.flag, setupEffect, h.read_reg]
  · intro s
    simp [setupEffect, Write.Full, Operand.Full]

def prologueEffect (s : RamState) : Effect :=
  { rip := 0x11c87f
    writes := [
      ⟨.mem (stackPtr s - 8), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 16), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 24), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 32), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 40), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨.reg 5, stackPtr s - 8⟩,
      ⟨.reg 4, stackPtr s - 56⟩,
      ⟨.reg 1, (Operand.reg 2 : Operand 64).read s⟩,
      ⟨.reg 2, (Operand.reg 6 : Operand 64).read s⟩,
      ⟨.reg 6, (Operand.reg 7 : Operand 64).read s⟩,
      ⟨.reg 8, (Operand.reg 2 : Operand 64).read s &&& (0xf0#8).signExtend 64⟩]
    flags := some (andFlags ((Operand.reg 2 : Operand 64).read s &&& (0xf0#8).signExtend 64)) }

theorem prologueEffect_of_save_setup {s saved t : RamState}
    (hs : (saveEffect s).Holds s saved) (ht : (setupEffect saved).Holds saved t) :
    (prologueEffect s).Holds s t := by
  have h := hs.seq setup_local (by simp [saveEffect, Write.Full, Operand.Full]) ht
  apply h.weaken
  · x86_norm [saveEffect, setupEffect, prologueEffect]
  · x86_norm [saveEffect, setupEffect, prologueEffect]
  · intro i; cases i <;> x86_norm [saveEffect, setupEffect, prologueEffect]
  · x86_norm [saveEffect, setupEffect, prologueEffect]

theorem savePre_of_callPre [Bindings] {s : RamState} (h : CallPre s) : SavePre s := by
  refine ⟨h.rip, ?_, ?_⟩
  · intro back hb
    have hb' : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 32 ∨ back = 40 := by simpa using hb
    apply h.frame.stack_sub_writable8 (by omega)
    rcases hb' with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro back hb i hi j hj he
    have hb' : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 32 ∨ back = 40 := by simpa using hb
    apply h.frame.stack_sub_avoids_code (offset := back) (len := 8) (by omega) (by omega) hi
    rw [he]
    have hsize : 0x1c86f ≤ Extracted.textBytes.size := by decide +kernel
    obtain ⟨byte, hm⟩ := text_program_mem_of_offset (0x1c860 + j) (by omega)
    have hm := P256.Proofs.Program.Compare.inProgram_of_mem hm
    simpa only [InProgram, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hm

theorem save_code {s : RamState} (h : CodeIn Extracted.programSections.toCodeMap s) :
    CodeIn (codeRange 0x11c860 saveBytes) s :=
  program_text_slice h 0x1c860 15 (by decide +kernel)

theorem setup_code {s : RamState} (h : CodeIn Extracted.programSections.toCodeMap s) :
    CodeIn (codeRange 0x11c86f setupBytes) s :=
  program_text_slice h 0x1c86f 16 (by decide +kernel)

theorem saveEffect_avoids_program [Bindings] {s : RamState} (h : CallFrame s 64) :
    (saveEffect s).Avoids Extracted.programSections.toCodeMap := by
  intro x hx c hc hcov
  have hstack (back : Nat) (hb : back ≤ 64) :
      ¬ (Component.mem (stackPtr s - BitVec.ofNat 64 back) 8).Covers x.1 := by
    rintro ⟨i, hi, he⟩
    apply h.stack_sub_avoids_code (offset := back) (len := 8) hb (by omega) hi
    rw [← he]
    exact P256.Proofs.Program.Compare.inProgram_of_mem hx
  simp only [saveEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, Write.component_reg, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact hstack 8 (by decide) hcov
    | exact hstack 16 (by decide) hcov
    | exact hstack 24 (by decide) hcov
    | exact hstack 32 (by decide) hcov
    | exact hstack 40 (by decide) hcov

theorem prologue [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (h : CallPre s)
    (outside : ∀ ip : BitVec 64, 0x11c860 ≤ ip.toNat → ip.toNat ≤ 0x11c87f →
      ip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ (prologueEffect s).Holds s t := by
  obtain ⟨n, saved, ha, hr, _, he⟩ := save boundary
    (fun ip hl hh ↦ outside ip hl (by omega)) s h.frame.ready (save_code h.frame.code)
    (savePre_of_callPre h)
  have hc := he.codeIn (saveEffect_avoids_program h.frame) h.frame.code
  obtain ⟨m, t, ha', hr', _, he'⟩ := setup boundary
    (fun ip hl hh ↦ outside ip (by omega) hh) saved hr (setup_code hc) he.rip
  have hc' := he'.codeIn (Effect.Avoids.of_noMem
    (by simp [setupEffect, Effect.components, Component.Covers]) _) hc
  exact ⟨n + m, t, ha.trans ha', hr', hc', prologueEffect_of_save_setup he he'⟩

end P256.Proofs.Program.Compare.Frame
