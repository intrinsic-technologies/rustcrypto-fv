import X86Proofs.Program.Execution
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Mov.Triple

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs

inductive PointerRegs where
  | rbxR14 | rbpR14 | r14R15
  deriving DecidableEq

def PointerRegs.outReg : PointerRegs → BitVec 5
  | .rbxR14 => 3
  | .rbpR14 => 5
  | .r14R15 => 14

def PointerRegs.inReg : PointerRegs → BitVec 5
  | .r14R15 => 15
  | _ => 14

def PointerRegs.outMov : PointerRegs → UInt8 × UInt8
  | .rbxR14 => (0x48, 0xdf)
  | .rbpR14 => (0x48, 0xef)
  | .r14R15 => (0x4c, 0xf7)

def PointerRegs.inModRM : PointerRegs → UInt8
  | .r14R15 => 0xfe
  | _ => 0xf6

theorem enterSquare [Bindings] (r : PointerRegs) (pc : BitVec 64) (d : BitVec 32)
    {s : RamState} {boundary : ReturnBoundary} (hready : ReadyToStep s) (hrip : s.RIP = pc)
    (hsp : stackPtr s ≠ boundary.rsp) (hpush : pushAddr s ≠ boundary.rsp)
    (hw : MemWritable s (pushAddr s) 8) (ha : RangeApart (pushAddr s) 8 (pc + 6) 5)
    (ho : CodeIn (codeRange pc [r.outMov.1, 0x89, r.outMov.2]) s)
    (hi : CodeIn (codeRange (pc + 3) [0x4c, 0x89, r.inModRM]) s)
    (hc : CodeIn (codeRange (pc + 6) (encodeCallRel32 d)) s)
    (htarget : branchTarget (pc + 6) 5 (d.signExtend 64) = 0x1145f0) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = 0x1145f0 ∧ stackPtr t = pushAddr s ∧ stackTop t = pc + 11 ∧
      t.regValue .rdi = (Operand.reg r.outReg : Operand 64).read s ∧
      t.regValue .rsi = (Operand.reg r.inReg : Operand 64).read s ∧
      AgreesExcept [.reg 4, .reg 6, .reg 7, .mem (pushAddr s) 8, .rip] s t := by
  obtain ⟨u, hsu, hru, hu⟩ := mov_r64_r64_effect_step pc r.outMov.1 r.outMov.2
    (by cases r <;> simp [RexWPrefix, PointerRegs.outMov]) (by cases r <;> decide) s hready ho hrip
  have huo : (movR64R64Effect pc 7 r.outReg s).Holds s u := by cases r <;> exact hu
  have heu : u.external = s.external := huo.agrees.external (by simp [Component.Covers])
  have hsuSp : stackPtr u = stackPtr s := huo.agrees.read (n := 64) (r := 4) (by simp)
  obtain ⟨v, huv, hrv, hv⟩ := mov_r64_r64_effect_step (pc + 3) 0x4c r.inModRM
    (by simp [RexWPrefix]) (by cases r <;> decide) u hru (hi.of_external_eq heu) huo.rip
  have hvi : (movR64R64Effect (pc + 3) 6 r.inReg u).Holds u v := by cases r <;> exact hv
  have hev : v.external = s.external := (hvi.agrees.external (by simp [Component.Covers])).trans heu
  have hsvSp : stackPtr v = stackPtr s :=
    (hvi.agrees.read (n := 64) (r := 4) (by simp)).trans hsuSp
  have hva : pushAddr v = pushAddr s := congrArg (· - 8) hsvSp
  obtain ⟨t, hvt, hrt, ht⟩ := call_rel32_effect_step (pc + 6) d (by rw [htarget]; decide)
    v hrv (hc.of_external_eq hev) ⟨by rw [hvi.rip]; change pc + 3 + 3 = pc + 6; rw [BitVec.add_assoc]; rfl,
    hva ▸ hw.of_external_eq hev, hva ▸ ha⟩
  have hstSp : stackPtr t = pushAddr s := ht.writes.1.trans hva
  have hreturn := (callEffect_stack ht).1
  have hframe := ht.agrees
  rw [pushEffect_components, hva] at hframe
  refine ⟨t, ((Advances.of_step hsu (.inr (fun h => hsp (hsuSp.symm.trans h)))).trans
    (Advances.of_step huv (.inr (fun h => hsp (hsvSp.symm.trans h))))).trans
      (Advances.of_step hvt (.inr (fun h => hpush (hstSp.symm.trans h)))), hrt, ht.rip.trans htarget, hstSp,
    by rw [hreturn, BitVec.add_assoc]; rfl, ?_, ?_, ?_⟩
  · exact (hframe.read (n := 64) (r := 7) (by simp)).trans
      ((hvi.agrees.read (n := 64) (r := 7) (by simp)).trans huo.writes)
  · exact (hframe.read (n := 64) (r := 6) (by simp)).trans
      (hvi.writes.trans (huo.agrees.read (n := 64) (r := r.inReg) (by cases r <;> simp [PointerRegs.inReg])))
  · exact ((huo.agrees.trans hvi.agrees).trans hframe).mono (by simp)

end K256.Proofs.Sec1.Sqrt
