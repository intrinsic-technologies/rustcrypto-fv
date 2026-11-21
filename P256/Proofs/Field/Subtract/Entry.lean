import P256.Proofs.Field.Interface
import P256.Proofs.Program.Push

set_option autoImplicit false

namespace P256.Proofs.Field.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prologueComponents (s : RamState) : List Component :=
  [.reg 4, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8, .mem (stackPtr s - 24) 8]

def prologueMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (s.external) (stackPtr s - 8) (s.regValue .r14)) (stackPtr s - 16) (s.regValue .rbx)) (stackPtr s - 24) (s.regValue .rax)

structure Entry [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 3 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x113f24
  rsp : stackPtr s = stackPtr initial - 24
  memory : s.external = prologueMemory initial
  agrees : AgreesExcept (prologueComponents initial) initial s

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : BinaryFieldPre s boundary 0x113f20 24) : ∃ t, Entry s t boundary := by
  let s0 := s
  have run0 : Advances boundary 0 s s0 := by simp only [advances_zero, s0]
  have ready0 : ReadyToStep s0 := readyToStep pre.machine pre.bindingsSupported
  have frame0 : AgreesExcept [.rip] s s0 := AgreesExcept.refl _ _
  have memory0 : s0.external = s.external := rfl
  have loaded0 : ProgramLoaded s0 := pre.loaded
  have rsp0 : stackPtr s0 = stackPtr s - 0 := by
    change stackPtr s = stackPtr s - 0#64
    rw [BitVec.sub_zero]
  have rip0 : s0.RIP = 0x113f20 := pre.rip
  obtain ⟨s1, run1, ready1, loaded1, rip1, rsp1, frame1, memory1⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready0 loaded0
      (frame0).grow 14 0 0x13f20 rsp0 rip0
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have value1 : (Operand.reg 14 : Operand 64).read s0 = s.regValue .r14 :=
    (frame0).read (by simp)
  obtain ⟨s2, run2, ready2, loaded2, rip2, rsp2, frame2, memory2⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready1 loaded1
      (frame0.trans frame1).grow 3 8 0x13f22 rsp1 rip1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have value2 : (Operand.reg 3 : Operand 64).read s1 = s.regValue .rbx :=
    (frame0.trans frame1).read (by simp)
  obtain ⟨s3, run3, ready3, loaded3, rip3, rsp3, frame3, memory3⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready2 loaded2
      (((frame0.trans frame1).trans frame2)).grow 0 16 0x13f23 rsp2 rip2
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have value3 : (Operand.reg 0 : Operand 64).read s2 = s.regValue .rax :=
    (((frame0.trans frame1).trans frame2)).read (by simp)
  refine ⟨s3, ⟨(((run0.trans run1).trans run2).trans run3), ready3, loaded3, rip3, rsp3, ?_, ?_⟩⟩
  · rw [memory3, memory2, memory1, memory0]
    change memStore (memStore (memStore (s.external) (stackPtr s - 8) ((Operand.reg 14 : Operand 64).read s0)) (stackPtr s - 16) ((Operand.reg 3 : Operand 64).read s1)) (stackPtr s - 24) ((Operand.reg 0 : Operand 64).read s2) = _
    rw [value1, value2, value3]
    rfl
  · apply ((((frame0.trans frame1).trans frame2).trans frame3)).mono
    simp only [prologueComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (((rfl | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) <;> simp

end P256.Proofs.Field.Subtract
