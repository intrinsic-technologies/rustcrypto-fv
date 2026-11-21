import P256.Proofs.Field.Montgomery.Prologue
import P256.Proofs.Field.Montgomery.SchoolbookPre
import P256.Proofs.Program.Call
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def entryComponents (s : RamState) : List Component :=
  [.reg 1, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8, .flags, .rip,
    .mem (stackPtr s - 8) 8, .mem (stackPtr s - 144) 8]

structure SchoolbookEntry [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (rightReg : Syntax.Reg := .rdx) (ret : BitVec 64 := 0x1138b3) : Prop where
  pre : SchoolbookPre s boundary
  execution : ∃ fuel, Advances boundary fuel initial s
  rsp : stackPtr s = stackPtr initial - 144
  destination : s.regValue .rdi = stackPtr initial - 72
  left : s.regValue .rsi = initial.regValue .rsi
  right : s.regValue .rcx = initial.regValue rightReg
  output : s.regValue .rbx = initial.regValue .rdi
  returnAddress : (returnBoundary s).rip = ret
  memory : s.external = memStore
    (memStore initial.external (stackPtr initial - 8) (initial.regValue .rbx))
    (stackPtr initial - 144) ret
  agrees : AgreesExcept (entryComponents initial) initial s

theorem schoolbook_entry_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : MultiplyPre s boundary) : ∃ t, SchoolbookEntry s t boundary := by
  obtain ⟨a, saved⟩ := save_correct pre
  obtain ⟨n, b, run, ready, _, effect⟩ := arguments boundary pre.outerBoundary a saved.ready
    (programText_slice (programLoaded_codeIn saved.loaded) 0x13898 argumentBytes
      (by decide +kernel) (by decide +kernel)) saved.rip
  have fb : AgreesExcept [.reg 1, .reg 3, .reg 7, .reg 2, .reg 8, .rip] a b := by
    simpa [argumentEffect, Effect.components, Write.component, Operand.component] using effect.agrees
  have mb := fb.external (by simp [Component.Covers])
  have loaded : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using saved.loaded
  have spb : stackPtr b = stackPtr s - 136 :=
    (fb.read (n := 64) (r := 4) (by simp)).trans saved.rsp
  obtain ⟨t, callRun, readyt, loadedt, callEffect, memory⟩ :=
    call_rel32_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready loaded
      (saved.agrees.trans fb).grow 136 0x138ae 0x90ad spb effect.rip
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
  have values : b.regValue .rcx = a.regValue .rdx ∧
      b.regValue .rbx = a.regValue .rdi ∧ b.regValue .rdi = stackPtr a + 64 ∧
      b.regValue .rdx = 4 ∧ b.regValue .r8 = 4 := effect.writes
  have left : t.regValue .rsi = s.regValue .rsi := total.read (n := 64) (r := 6)
    (by simp [entryComponents])
  have right : t.regValue .rcx = s.regValue .rdx :=
    ((ft.read (n := 64) (r := 1) (by simp)).trans values.1).trans
      (saved.agrees.read (n := 64) (r := 2) (by simp [saveComponents]))
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
  have ret : (returnBoundary t).rip = 0x1138b3 := (callEffect_stack callEffect).1
  have schoolpre := schoolbook_pre pre.toCalleePre pre.rightBounded pre.rightAllocated pre.rightStack
    (bindingsSupported_of_ready_agrees pre.bindingsSupported readyt total)
    (supportedMachine_of_ready_agrees pre.machine readyt total)
    (total.directionFlagClear (by simp [entryComponents]) pre.directionFlag)
    loadedt callEffect.rip rsp left right dst lengthL lengthR total.grow
    (by rw [ret]; exact inProgram_of_textOffset 0x138b3 (by decide))
  refine ⟨t, ⟨schoolpre, ⟨2+n+1, (saved.execution.trans run).trans callRun⟩,
    rsp, dst, left, right, output, ret, ?_, total⟩⟩
  rw [memory, mb, saved.memory]
  rfl

end P256.Proofs.Field.Montgomery
