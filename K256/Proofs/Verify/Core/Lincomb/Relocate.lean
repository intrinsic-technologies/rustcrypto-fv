import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)



inductive CopySite where
  | peerTable | peerDigits | generator | peer
  deriving DecidableEq

namespace CopySite

def start : CopySite → Label
  | .peerTable => .l10fc13
  | .peerDigits => .l10fc29
  | .generator => .l10fc3c
  | .peer => .l10fc4f

def next : CopySite → Label
  | .peerTable => .l10fc29
  | .peerDigits => .l10fc3c
  | .generator => .l10fc4f
  | .peer => .l10fc62

def ret : CopySite → BitVec 64
  | .peerTable => 0x10fc29
  | .peerDigits => 0x10fc3c
  | .generator => 0x10fc4f
  | .peer => 0x10fc62

def src : CopySite → Nat
  | .peerTable => 0x1568
  | .peerDigits => 8
  | .generator => 0xbc8
  | .peer => 0x228

def dst : CopySite → Nat
  | .peerTable => 0x228
  | .peerDigits => 0x9a8
  | .generator => 0x1568
  | .peer => 0x1f08

def len : CopySite → Nat
  | .peerTable => 0x780
  | .peerDigits => 0x220
  | .generator => 0x9a0
  | .peer => 0x9a0


structure RegistersAt (fr : Activation) (b : Registers) : Prop where
  digits : b[5] = ⟨64,slot fr 8⟩
  memcpy : b[12] = ⟨64,0x12a820⟩
  table : b[13] = ⟨64,slot fr 0x1568⟩

private theorem setup (site : CopySite) {fr : Activation} {b : Registers} {m : Ram}
    (slots : RegistersAt fr b) (sp : b[4].get 64 = workSp fr)
    (r14 : site ≠ .peerTable → b[14] = ⟨64,slot fr 0x228⟩)
    (w : Writable Extracted.programImage m (workSp fr - 8) 8) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨site.start,b,m⟩ =
      .call ⟨.l12a820,c,memStore m (workSp fr - 8) site.ret⟩ (callResume site.next site.ret) ∧
      c[4].get 64 = workSp fr - 8 ∧ c[7].get 64 = slot fr site.dst ∧
      c[6].get 64 = slot fr site.src ∧ c[2].get 64 = BitVec.ofNat 64 site.len ∧
      c[14] = ⟨64,slot fr 0x228⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,15,22,39,50,51] → c[i] = b[i]) := by
  have table := congrArg (Value.get 64) slots.table
  have digits := congrArg (Value.get 64) slots.digits
  have memcpy := congrArg (Value.get 64) slots.memcpy
  change b[13].get 64 = slot fr 0x1568 at table
  change b[5].get 64 = slot fr 8 at digits
  change b[12].get 64 = 0x12a820 at memcpy
  cases site <;> simp only [start, next, dst, src, len, ret]
  all_goals try
    have h14 := r14 (by decide)
    have read14 := congrArg (Value.get 64) h14
    change b[14].get 64 = slot fr 0x228 at read14
  all_goals
    refine ⟨?_, ?run, ?post⟩
    case run =>
      first | cfg_eval [sp, memcpy, table, digits, read14] | cfg_eval [sp, memcpy, table, digits]
      refine Eq.trans (ite_eq_left ?_) ?_
      · first | slot_guard using code_l10fc13 | slot_guard using code_l10fc29
              | slot_guard using code_l10fc3c | slot_guard using code_l10fc4f
      · rfl
    case post =>
      refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · first | exact h14 | rfl
      · rintro ⟨i,hi⟩ live
        simp only [List.mem_cons, List.not_mem_nil, or_false] at live
        rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem step (site : CopySite) {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m n : Ram} (e : Entry fr a p digest r s) (whole : RamWriteFrame fr.original n [fr.region])
    (f : CallerFrame fr c b m n) (regs : RegistersAt fr b)
    (r14 : site ≠ .peerTable → b[14] = ⟨64,slot fr 0x228⟩) (df : c[22].get 1 = 0) :
    ∃ d t, Reaches site.start b n site.next d t ∧ CallerFrame fr c d m t ∧ RegistersAt fr d ∧
      d[14] = ⟨64,slot fr 0x228⟩ ∧ Copied n (slot fr site.src) t (slot fr site.dst) site.len ∧
      RamWriteFrame n t (workWrites fr 8 site.dst site.len) := by
  obtain ⟨x, call, sp, di, si, dx, next14, keep⟩ := setup site regs (congrArg (Value.get 64) f.sp)
    r14 (belowWrite e whole (by decide))
  have dir : x[22].get 1 = 0 :=
    (congrArg (Value.get 1) ((keep 22 (by decide)).trans (f.fixedRegs 22 (by decide)))).trans df
  obtain ⟨d,t,reach,rsp,pres,copied,frame⟩ := copyCall e whole
    (by cases site <;> decide) (by cases site <;> decide) (by cases site <;> decide)
    (by cases site <;> decide) call sp di si dx dir
  have saved (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,15,22,39,50,51]) : d[i] = b[i] :=
    (pres i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans (keep i h)
  have new14 := (pres 14 (by decide)).trans next14
  refine ⟨d,t,reach,CallerFrame.next e f (by decide) (by cases site <;> decide) (by cases site <;> decide)
    frame rsp ?_ ?_, ⟨(saved 5 (by decide)).trans regs.digits, (saved 12 (by decide)).trans regs.memcpy,
      (saved 13 (by decide)).trans regs.table⟩, new14, copied, frame⟩
  · intro i h
    by_cases he : i.val = 14
    · have eq : i = 14 := Fin.ext he
      subst i
      exact congrArg Value.width new14
    · rw [saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)]
      exact f.widths i h
  · intro i h
    exact saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)

end CopySite
end K256.Proofs.Verify.Core.Lincomb
