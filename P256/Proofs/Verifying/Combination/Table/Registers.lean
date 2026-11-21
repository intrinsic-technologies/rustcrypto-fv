import P256.Proofs.Verifying.Combination.Table.Copy
import P256.Proofs.Verifying.Combination.Table.Source

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Registers (s t : RamState) : Prop where
  rbx : t.regValue .rbx = s.regValue .rdi
  r12 : t.regValue .r12 = stackPtr s - 320
  r14 : t.regValue .r14 = stackPtr s - 224
  r15 : t.regValue .r15 = stackPtr s - 1088

theorem Registers.agrees {s t u : RamState} {cs : List Component}
    (regs : Registers s t) (agrees : AgreesExcept cs t u)
    (rbx : .reg 3 ∉ cs) (r12 : .reg 12 ∉ cs) (r14 : .reg 14 ∉ cs) (r15 : .reg 15 ∉ cs) :
    Registers s u :=
  ⟨(agrees.read (n := 64) (r := 3) rbx).trans regs.rbx,
    (agrees.read (n := 64) (r := 12) r12).trans regs.r12,
    (agrees.read (n := 64) (r := 14) r14).trans regs.r14,
    (agrees.read (n := 64) (r := 15) r15).trans regs.r15⟩

theorem Registers.abi {s t u : RamState}
    (regs : Registers s t)
    (abi : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) :
    Registers s u :=
  ⟨(abi .rbx (by simp)).trans regs.rbx, (abi .r12 (by simp)).trans regs.r12,
    (abi .r14 (by simp)).trans regs.r14, (abi .r15 (by simp)).trans regs.r15⟩

theorem copy_source [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {value : Projective}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (slot : Slot) (src : Source) (ne : src ≠ some slot)
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 (offset slot))
    (source : t.regValue .rsi = sourceAddress s point src)
    (count : t.regValue .rcx = 12)
    (input : ProjectiveAt t (sourceAddress s point src) value) :
    ∃ u, Advances boundary 12 t u ∧ Memory s u cursor point (writeCell cells slot value) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + 3#64 ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1,
        .mem (stackPtr s - BitVec.ofNat 64 (offset slot)) 96, .rip] t u := by
  exact copy_cells pre state slot codeOffset codeBound codeBytes rip dst count
    (source ▸ source_readable pre state.toFrameState src)
    (by rw [source, dst]; exact source_disjoint pre src slot ne)
    (source ▸ input)

end P256.Proofs.Verifying.Combination.Table
