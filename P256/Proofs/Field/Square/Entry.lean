import P256.Proofs.Field.Square.Arguments
import P256.Proofs.Field.Montgomery.Entry
import P256.Proofs.Field.Montgomery.SchoolbookPre
import P256.Proofs.Program.Call
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Field.Square

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Montgomery
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem schoolbook_entry_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113800 32 32 280) : ∃ t, SchoolbookEntry s t boundary .rsi 0x113823 := by
  obtain ⟨a, saved⟩ := save_correct_at true pre
  obtain ⟨n, b, run, ready, _, effect⟩ := Square.arguments boundary pre.outerBoundary a saved.ready
    (programText_slice (programLoaded_codeIn saved.loaded) 0x13808 Square.argumentBytes
      (by decide +kernel) (by decide +kernel)) saved.rip
  have fb : AgreesExcept [.reg 1, .reg 3, .reg 7, .reg 2, .reg 8, .rip] a b := by
    simpa [Square.argumentEffect, Effect.components, Write.component, Operand.component] using effect.agrees
  have mb := fb.external (by simp [Component.Covers])
  have loaded : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using saved.loaded
  have spb : stackPtr b = stackPtr s - 136 :=
    (fb.read (n := 64) (r := 4) (by simp)).trans saved.rsp
  obtain ⟨t, callRun, readyt, loadedt, callEffect, memory⟩ :=
    call_rel32_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready loaded
      (saved.agrees.trans fb).grow 136 0x1381e 0x913d spb effect.rip
      (by decide) (by decide) (by decide) (by decide +kernel)
      (inProgram_of_textOffset 0x1c960 (by decide))
  have push : pushAddr b = stackPtr s - 144 := by
    rw [pushAddr, spb, BitVec.sub_sub]
    rfl
  have ft : AgreesExcept [.reg 4, .mem (stackPtr s - 144) 8, .rip] b t := by
    simpa only [pushEffect_components, push] using callEffect.agrees
  have total : AgreesExcept (entryComponents s) s t := by
    apply (saved.agrees.trans (fb.trans ft)).mono
    simp only [saveComponents, entryComponents, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (rfl | rfl | rfl | rfl) |
      ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) <;> simp
  have rsp : stackPtr t = stackPtr s - 144 := callEffect.writes.1.trans push
  have values : b.regValue .rcx = a.regValue .rsi ∧
      b.regValue .rbx = a.regValue .rdi ∧ b.regValue .rdi = stackPtr a + 64 ∧
      b.regValue .rdx = 4 ∧ b.regValue .r8 = 4 := effect.writes
  have left : t.regValue .rsi = s.regValue .rsi := total.read (n := 64) (r := 6)
    (by simp [entryComponents])
  have right : t.regValue .rcx = s.regValue .rsi :=
    ((ft.read (n := 64) (r := 1) (by simp)).trans values.1).trans
      (saved.agrees.read (n := 64) (r := 6) (by simp [saveComponents]))
  have output : t.regValue .rbx = s.regValue .rdi :=
    ((ft.read (n := 64) (r := 3) (by simp)).trans values.2.1).trans
      (saved.agrees.read (n := 64) (r := 7) (by simp [saveComponents]))
  have dst : t.regValue .rdi = stackPtr s - 72 := by
    have h := (ft.read (n := 64) (r := 7) (by simp)).trans values.2.2.1
    change t.regValue .rdi = stackPtr a + 64 at h
    rw [h, saved.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have lengthL : t.regValue .rdx = 4 :=
    (ft.read (n := 64) (r := 2) (by simp)).trans values.2.2.2.1
  have lengthR : t.regValue .r8 = 4 :=
    (ft.read (n := 64) (r := 8) (by simp)).trans values.2.2.2.2
  have ret : (returnBoundary t).rip = 0x113823 := (callEffect_stack callEffect).1
  have schoolpre := schoolbook_pre pre pre.inputBounded pre.inputAllocated
    (pre.separation (0 : Fin 3) (2 : Fin 3) (by decide))
    (bindingsSupported_of_ready_agrees pre.bindingsSupported readyt total)
    (supportedMachine_of_ready_agrees pre.machine readyt total)
    (total.directionFlagClear (by simp [entryComponents]) pre.directionFlag)
    loadedt callEffect.rip rsp left right dst lengthL lengthR total.grow
    (by rw [ret]; exact inProgram_of_textOffset 0x13823 (by decide))
  refine ⟨t, ⟨schoolpre, ⟨2+n+1, (saved.execution.trans run).trans callRun⟩,
    rsp, dst, left, right, output, ret, ?_, total⟩⟩
  rw [memory, mb, saved.memory]
  rfl

end P256.Proofs.Field.Square
