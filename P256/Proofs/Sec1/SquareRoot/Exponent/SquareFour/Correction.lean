import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Borrow
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Prefix
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Dead
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Select
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Preserve

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hc : ExponentConstants s t x)
    (rip : t.RIP = 0x11568e)
    (mod0 : (Operand.reg 11 : Operand 64).read t = -1)
    (mod1 : (Operand.reg 3 : Operand 64).read t = 0xffffffff) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧ ExponentConstants s u x ∧
      u.RIP = 0x11580d ∧
      ReverseWordsAt u (exponentFrameBase s)
        (words (reduce (inputLimbs t) ((Operand.reg 15 : Operand 64).read t))) ∧
      AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨b,nb,rb,fb,eb,ab⟩ := borrow_run ctx hf rip
  obtain ⟨d0,d1,d2,d3,db,l3,l2,l0,l1⟩ := borrow_values hf hc mod0 mod1 eb
  obtain ⟨p,rp,fp,ip,qp,ap⟩ := prefix_correct ctx fb eb.rip
  obtain ⟨d,nd,rd,fd,ed,ad⟩ := dead_run ctx fp ip
  have ag : AgreesExcept [.reg 8,.reg 10,.flags,.rip,
      .mem (exponentFrameBase s + 8) 1,.mem (exponentFrameBase s + 8) 8] b d := by
    have sp : (Operand.reg 4#5 : Operand 64).read p = exponentFrameBase s := fp.rsp
    exact (ap.trans ed.agrees).mono (by simp [deadEffect,Effect.components,sp])
  have q : ((Operand.reg 8 : Operand 8).read d).setWidth 64 =
      selector ((Operand.reg 15 : Operand 64).read t) (subRaw (inputLimbs t) modulus).2 := by
    have hd : (Operand.reg 8 : Operand 8).read d = (Operand.reg 8 : Operand 8).read p :=
      ed.agrees.read (by simp [deadEffect,Effect.components])
    rw [hd,qp,ab.read (r := 15) (n := 64) (by simp [components])]
    have db8 := congrArg (BitVec.setWidth 8) db
    change (Operand.reg 9 : Operand 8).read b = _ at db8
    rw [db8]
    exact selector_byte _ _ (eq_zero_or_one (subRaw_toNat (inputLimbs t) modulus).1)
  have keep (r : BitVec 5) (hr : r ∈ ([0,1,2,5,6,7,13] : List (BitVec 5))) :
      (Operand.reg r : Operand 64).read d = (Operand.reg r : Operand 64).read b := by
    apply ag.read
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have keep2 : (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read d =
      (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read b := by
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc hcover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    all_goals obtain ⟨j,hj,he⟩ := hcover
    all_goals exact OffsetsApart.ne (base := exponentFrameBase s) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  obtain ⟨u,nu,ru,fu,eu,au⟩ := select_run ctx fd ed.rip
  have value := select_values fd eu
  rw [q,keep 0 (by simp),keep 1 (by simp),keep 2 (by simp),keep 5 (by simp),
    keep 6 (by simp),keep 7 (by simp),keep 13 (by simp),keep2,d0,d1,d2,d3,l0,l1,l2,l3] at value
  have total := trans (trans (trans ab (ap.mono (by simp [components]))) ad) au
  exact ⟨u,_,((rb.trans rp).trans rd).trans ru,fu,
    constants_of_agrees ctx hc (agrees_wide total),eu.rip,value,total⟩

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
