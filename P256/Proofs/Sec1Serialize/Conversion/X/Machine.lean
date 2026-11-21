import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Canonical
import P256.Proofs.Sec1Serialize.Conversion.X.Round1
import P256.Proofs.Sec1Serialize.Conversion.X.Round2
import P256.Proofs.Sec1Serialize.Conversion.X.Round3
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

namespace P256.Proofs.Sec1Serialize.Conversion
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem x_machine [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110d88) (rsi : t.regValue .rsi = s.regValue .rsi)
    (r14 : t.regValue .r14 = s.regValue .rsi) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110ea5 ∧
      (u.regValue .rbx, u.regValue .r15, u.regValue .r12, u.regValue .r13) =
        compilerConversionBV
          ((Operand.mem (s.regValue .rsi) : Operand 64).read t)
          ((Operand.mem (s.regValue .rsi + 8) : Operand 64).read t)
          ((Operand.mem (s.regValue .rsi + 16) : Operand 64).read t)
          ((Operand.mem (s.regValue .rsi + 24) : Operand 64).read t) ∧
      u.regValue .r9 = 0xffffffff00000001 ∧ AgreesExcept xRegisters t u := by
  have agree {a b c : RamState} (ha : AgreesExcept xRegisters a b)
      (hb : AgreesExcept xRegisters b c) : AgreesExcept xRegisters a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have read_mem {a b : RamState} (h : AgreesExcept xRegisters a b) (addr : BitVec 64) :
      (Operand.mem addr : Operand 64).read b = (Operand.mem addr : Operand 64).read a :=
    read_mem_of_agrees h addr (by simp [xRegisters, Component.Covers])
  have pointer {a b : RamState} (h : AgreesExcept xRegisters a b) :
      b.regValue .r14 = a.regValue .r14 :=
    h.read (n := 64) (r := 14) (by simp [xRegisters])
  obtain ⟨v0, st0, ip0, hv0, hk0, hz0, ag0⟩ := x_initial pre stage rip rsi
  obtain ⟨v1, st1, ip1, hv1, hk1, ag1⟩ :=
    x_round1 pre st0 ip0 ((pointer ag0).trans r14) hk0 hz0
  obtain ⟨v2, st2, ip2, hv2, hk2, hm2, hh2, ag2⟩ :=
    x_round2 pre st1 ip1 ((pointer (agree ag0 ag1)).trans r14) hk1
  obtain ⟨u, stu, ipu, hv3, hku, ag3⟩ :=
    x_round3 pre st2 ip2 ((pointer (agree ag0 (agree ag1 ag2))).trans r14) hk2 hm2 hh2
  refine ⟨u, stu, ipu, ?_, hku, agree ag0 (agree ag1 (agree ag2 ag3))⟩
  obtain ⟨h00, h01, h02, h03⟩ := hv0
  rw [h00, h01, h02, h03, read_mem ag0] at hv1
  have h10 := congrArg Prod.fst hv1
  have h11 := congrArg (fun v => v.2.1) hv1
  have h12 := congrArg (fun v => v.2.2.1) hv1
  have h13 := congrArg (fun v => v.2.2.2) hv1
  dsimp only at h10 h11 h12 h13
  rw [h10, h11, h12, h13, read_mem (agree ag0 ag1)] at hv2
  have h20 := congrArg Prod.fst hv2
  have h21 := congrArg (fun v => v.2.1) hv2
  have h22 := congrArg (fun v => v.2.2.1) hv2
  have h23 := congrArg (fun v => v.2.2.2) hv2
  dsimp only at h20 h21 h22 h23
  rw [h20, h21, h22, h23, read_mem (agree ag0 (agree ag1 ag2))] at hv3
  exact hv3

end P256.Proofs.Sec1Serialize.Conversion
