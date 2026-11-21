import P256.Proofs.Field.Interface
import P256.Proofs.Program.SaveRegisters

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prologueComponents (s : RamState) : List Component :=
  saveFrame s ++ [.mem (stackPtr s - 56) 8]

structure Entry [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 7 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x113c1b
  rsp : stackPtr s = stackPtr initial - 56
  memory : s.external = memStore (saveMemory initial) (stackPtr initial - 56)
    (initial.regValue .rax)
  agrees : AgreesExcept (prologueComponents initial) initial s

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : BinaryFieldPre s boundary 0x113c10 56) : ∃ t, Entry s t boundary := by
  have code : SaveCode 0x13c10 := by constructor <;> decide +kernel
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, frame⟩ :=
    save_registers (codeOffset := 0x13c10) pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide) pre.rip code
  obtain ⟨t, run2, readyt, loadedt, ript, rspt, framet, memoryt⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready loaded frame.grow
      0 48 0x13c1a rsp rip (by decide) (by decide) (by decide) (by decide +kernel)
  have a : (Operand.reg 0 : Operand 64).read u = s.regValue .rax :=
    frame.read (by simp [saveFrame])
  refine ⟨t, ⟨run.trans run2, readyt, loadedt, ript, rspt, ?_, ?_⟩⟩
  · rw [memoryt, memory]
    change memStore (saveMemory s) (stackPtr s - 56) ((Operand.reg 0 : Operand 64).read u) = _
    rw [a]
  · apply (frame.trans framet).mono
    simp only [prologueComponents, saveFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl) <;> simp

end P256.Proofs.Field.Montgomery.Reduction
