import P256.Proofs.Program.Push
import P256.Proofs.Program.Interface
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedMemory (s : RamState) : Ram :=
  memStore (memStore (memStore s.external (stackPtr s - 8) (s.regValue .r15))
    (stackPtr s - 16) (s.regValue .r14)) (stackPtr s - 24) (s.regValue .rbx)

def saveComponents (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s - 8) 8,
    .mem (stackPtr s - 16) 8, .mem (stackPtr s - 24) 8]

theorem stack_setup [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary} {inputBytes : Nat}
    (pre : CalleePre s boundary 0x109d00 inputBytes 72 1552) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x109d0c ∧ stackPtr t = stackPtr s - 328 ∧
      t.external = savedMemory s ∧
      AgreesExcept (saveComponents s) s t := by
  obtain ⟨s1, a1, r1, l1, i1, p1, f1, m1⟩ :=
    P256.Proofs.Program.push_exists pre.stack
      (pre.avoids (Stack.region s 1552) (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h) 15 0 0x9d00
      (by simp) pre.rip (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  obtain ⟨s2, a2, r2, l2, i2, p2, f2, m2⟩ :=
    P256.Proofs.Program.push_exists pre.stack
      (pre.avoids (Stack.region s 1552) (by simp)) pre.outerBoundary r1 l1 f1.grow 14 8 0x9d02
      p1 i1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  obtain ⟨s3, a3, r3, l3, i3, p3, f3, m3⟩ :=
    P256.Proofs.Program.push_exists pre.stack
      (pre.avoids (Stack.region s 1552) (by simp)) pre.outerBoundary r2 l2
      (f1.trans f2).grow 3 16 0x9d04 p2 i2
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, a4, ready, effect⟩ :=
    (sub_r64_imm32_effect_step 0x109d05 0x48 0xec 304
      (by constructor <;> decide +kernel) rfl rfl).advances r3
      (programText_slice (programLoaded_codeIn l3) 0x9d05 _
        (by decide +kernel) (by decide +kernel)) i3
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9d0c (by decide +kernel)))
  have f4 : AgreesExcept [.reg 4, .flags, .rip] s3 t := effect.agrees
  have ext : t.external = s3.external := f4.external (by simp [Component.Covers])
  refine ⟨t, ((a1.trans a2).trans a3).trans a4, ready, ?_, effect.rip, ?_, ?_, ?_⟩
  · intro a b h
    rw [ext]
    exact l3 a b h
  · have hw : stackPtr t = stackPtr s3 - 304 := effect.writes
    rw [hw, p3, BitVec.sub_sub]
    rfl
  · have bx : (Operand.reg 3 : Operand 64).read s2 = s.regValue .rbx :=
      (f1.trans f2).read (by simp)
    have r14 : (Operand.reg 14 : Operand 64).read s1 = s.regValue .r14 :=
      f1.read (by simp)
    rw [ext, m3, m2, m1]
    change memStore (memStore (memStore s.external (stackPtr s - 8) (s.regValue .r15))
      (stackPtr s - 16) ((Operand.reg 14 : Operand 64).read s1))
      (stackPtr s - 24) ((Operand.reg 3 : Operand 64).read s2) = _
    rw [bx, r14]
    rfl
  · exact (((f1.trans f2).trans f3).trans f4).mono (by simp [saveComponents])

end P256.Proofs.SignatureFromDer.Decode
