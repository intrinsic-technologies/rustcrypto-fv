import Base16ct.Proofs.EncodeStr.Upper.Epilogue.Return
import Base16ct.Proofs.EncodeStr.Upper.Machine
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple

namespace Base16ct.Proofs.EncodeStr.Upper.Epilogue
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem failure_run [Bindings] {initial s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = 0x10048d) (hsp : stackPtr s = stackPtr initial - 24)
    (hm : MemReadable s (stackPtr initial - 16) 1)
    (hb : (Operand.mem (stackPtr initial - 16) : Operand 8).read s = 1)
    (hmb : MemReadable s (stackPtr initial - 8) 8)
    (hbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx)
    (hmret : MemReadable s (stackPtr initial) 8)
    (hv : (Operand.mem (stackPtr initial) : Operand 64).read s = (returnBoundary initial).rip)
    (hl : (returnBoundary initial).rip.toNat < 2^32)
    (ho : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, Returns (returnBoundary initial) 6 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 0, .reg 1, .reg 3, .reg 4, .flags, .rip] s t ∧
      t.regValue .rax = 1 ∧ t.regValue .rbx = initial.regValue .rbx := by
  have haddr : stackPtr s + 8 = stackPtr initial - 16 := by
    rw [hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hc1 : CodeIn (codeRange 0x10048d [0x0f, 0xb6, 0x4c, 0x24, 8]) s := by
    have hbytes : Extracted.textBytes.toListFrom 0x48d 5 = [0x0f, 0xb6, 0x4c, 0x24, 8] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x48d = 0x10048d by decide +kernel]
      using program_text_slice hc 0x48d 5 (by decide +kernel)
  obtain ⟨u, run1, ready1, e1⟩ := (movzx_r32_m8_effect_step 0x10048d 1 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid]) rfl rfl).advances hr hc1
    ⟨hip, by change MemReadable s (stackPtr s + 8) 1; rw [haddr]; exact hm⟩ (text_address_ne_return ho 0x492 (by decide +kernel))
  have a1 : AgreesExcept [.reg 1, .rip] s u := e1.agrees
  have mem1 : u.external = s.external :=
    (a1.external (by simp [Component.Covers]))
  have hc2 : CodeIn (codeRange 0x100492 [0xb8, 2, 0, 0, 0]) u := by
    have hbytes : Extracted.textBytes.toListFrom 0x492 5 = [0xb8, 2, 0, 0, 0] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x492 = 0x100492 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem1) 0x492 5 (by decide +kernel)
  obtain ⟨v, run2, ready2, e2⟩ := (mov_r32_imm32_effect_step 0x100492 0xb8 (by decide +kernel) 2).advances ready1 hc2
    e1.rip (text_address_ne_return ho 0x497 (by decide +kernel))
  have a2 : AgreesExcept [.reg 0, .rip] u v := e2.agrees
  have mem2 : v.external = s.external :=
    (a2.external (by simp [Component.Covers])).trans mem1
  have hc3 : CodeIn (codeRange 0x100497 [0x29, 0xc8]) v := by
    have hbytes : Extracted.textBytes.toListFrom 0x497 2 = [0x29, 0xc8] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x497 = 0x100497 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem2) 0x497 2 (by decide +kernel)
  obtain ⟨w, run3, ready3, e3⟩ := (sub_r32_r32_effect_step 0x100497 0xc8 rfl).advances ready2 hc3
    e2.rip (text_address_ne_return ho 0x499 (by decide +kernel))
  have a3 : AgreesExcept [.reg 0, .flags, .rip] v w := e3.agrees
  have mem3 : w.external = s.external :=
    (a3.external (by simp [Component.Covers])).trans mem2
  have rsp3 : stackPtr w = stackPtr initial - 24 :=
    ((a1.trans a2).trans a3).read (n := 64) (r := 4) (by simp) |>.trans hsp
  have hc4 : CodeIn (codeRange 0x100499 [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3]) w := by
    have hbytes : Extracted.textBytes.toListFrom 0x499 6 = [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x499 = 0x100499 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem3) 0x499 6 (by decide +kernel)
  obtain ⟨t, run4, ready4, a4, bx4⟩ := restore_return 0x100499 ready3 hc4 e3.rip rsp3
    ⟨hmb.low, fun i hi => mem3 ▸ hmb.mem i hi⟩
    (by change memLoad w.external _ 64 = _; rw [mem3]; exact hbx)
    ⟨hmret.low, fun i hi => mem3 ▸ hmret.mem i hi⟩
    (by change memLoad w.external _ 64 = _; rw [mem3]; exact hv) hl
  refine ⟨t, ((run1.trans run2).trans run3).returns run4, ready4,
    (((a1.trans a2).trans a3).trans a4).mono (by simp), ?_, bx4⟩
  have hcx : u.regValue .rcx = 1 := by
    have hw := e1.writes
    change u.regValue .rcx = ((Operand.mem (stackPtr s + 8) : Operand 8).read s).setWidth 64 at hw
    rw [haddr, hb] at hw
    exact hw
  have hvax : v.regValue .rax = 2 := e2.writes
  have hvcx : v.regValue .rcx = 1 :=
    (a2.read (n := 64) (r := 1) (by simp)).trans hcx
  have hwax : w.regValue .rax = 1 := by
    have hw := e3.writes
    change w.regValue .rax = ((v.regValue .rax).setWidth 32 - (v.regValue .rcx).setWidth 32).setWidth 64 at hw
    rw [hvax, hvcx] at hw
    exact hw
  exact (a4.read (n := 64) (r := 0) (by simp)).trans hwax

end Base16ct.Proofs.EncodeStr.Upper.Epilogue
