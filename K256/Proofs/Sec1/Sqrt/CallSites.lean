import K256.Proofs.Sec1.Sqrt.Call
import K256.Proofs.Common.Machine
import X86Proofs.Program.Entry

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program

theorem textSlice {s : RamState}
    (h : CodeIn Extracted.programSections.toCodeMap s) (offset : Nat) (bytes : List UInt8)
    (hsize : offset + bytes.length ≤ 174527)
    (hbytes : Extracted.textBytes.toListFrom offset bytes.length = bytes) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) s := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset bytes.length
    (by simpa only [Common.textBytes_size] using hsize)
  simpa only [hbytes] using hs

structure SquareCallSite where
  offset : Nat
  regs : PointerRegs
  deriving DecidableEq

def squareCallSites : List SquareCallSite :=
  let runs : List (Nat × Nat × PointerRegs) :=
    [(0x16293, 3, .rbxR14), (0x1673c, 3, .rbxR14), (0x16bcd, 2, .rbxR14),
     (0x17034, 11, .rbpR14), (0x176e7, 22, .rbxR14), (0x18040, 1, .r14R15),
     (0x184d0, 1, .rbxR14), (0x18950, 1, .rbxR14), (0x18d97, 3, .rbxR14),
     (0x1924d, 23, .rbxR14), (0x19b89, 6, .rbxR14), (0x1a105, 2, .rbxR14)]
  runs.flatMap fun (start, count, regs) =>
    (List.range count).map fun i => ⟨start + 60 * i, regs⟩

namespace SquareCallSite

def pc (c : SquareCallSite) : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 c.offset

def disp (c : SquareCallSite) : BitVec 32 := (0x1145f0 - (c.pc + 11)).setWidth 32

private abbrev Checked (c : SquareCallSite) :=
  c.offset + 11 ≤ 174527 ∧
  Extracted.textBytes.toListFrom c.offset 3 = [c.regs.outMov.1, 0x89, c.regs.outMov.2] ∧
  Extracted.textBytes.toListFrom (c.offset + 3) 3 = [0x4c, 0x89, c.regs.inModRM] ∧
  Extracted.textBytes.toListFrom (c.offset + 6) 5 = encodeCallRel32 c.disp ∧
  branchTarget (c.pc + 6) 5 (c.disp.signExtend 64) = 0x1145f0

private theorem checked : squareCallSites.all (fun c => decide c.Checked) = true := by
  decide +kernel

theorem enter [Bindings] {c : SquareCallSite} (hc : c ∈ squareCallSites)
    {s : RamState} {boundary : ReturnBoundary} (hready : ReadyToStep s) (hrip : s.RIP = c.pc)
    (hsp : stackPtr s ≠ boundary.rsp) (hpush : pushAddr s ≠ boundary.rsp)
    (hw : MemWritable s (pushAddr s) 8) (ha : RangeApart (pushAddr s) 8 (c.pc + 6) 5)
    (hcode : CodeIn Extracted.programSections.toCodeMap s) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = 0x1145f0 ∧ stackPtr t = pushAddr s ∧ stackTop t = c.pc + 11 ∧
      t.regValue .rdi = (Operand.reg c.regs.outReg : Operand 64).read s ∧
      t.regValue .rsi = (Operand.reg c.regs.inReg : Operand 64).read s ∧
      AgreesExcept [.reg 4, .reg 6, .reg 7, .mem (pushAddr s) 8, .rip] s t := by
  have h : c.Checked := of_decide_eq_true (List.all_eq_true.mp checked c hc)
  obtain ⟨hlen, ho, hi, hcall, ht⟩ := h
  apply enterSquare c.regs c.pc c.disp hready hrip hsp hpush hw ha _ _ _ ht
  · exact textSlice hcode c.offset _ (by change c.offset + 3 ≤ _; omega) ho
  · have h := textSlice hcode (c.offset + 3) [0x4c, 0x89, c.regs.inModRM]
      (by change c.offset + 3 + 3 ≤ _; omega) hi
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  · have h := textSlice hcode (c.offset + 6) (encodeCallRel32 c.disp)
      (by change c.offset + 6 + 5 ≤ _; omega) hcall
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h

end SquareCallSite

end K256.Proofs.Sec1.Sqrt
