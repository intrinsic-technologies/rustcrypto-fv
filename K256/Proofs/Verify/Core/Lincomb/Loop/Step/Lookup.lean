import K256.Proofs.Verify.Core.Lincomb.Loop.ColumnFrame
import K256.Proofs.Verify.Core.Lincomb.Loop.Index

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

private theorem jump {l r : Label} {a b : Registers} {m : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨r,b,m⟩) :
    Reaches l a m r b m := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  rw [step]
  rfl

private theorem lookupRow {a : Registers} {m : Ram} {sp row : BitVec 64} {i : Nat}
    (rsp : a[4].get 64 = sp) (component : a[12].get 64 = BitVec.ofNat 64 i)
    (base : a[13].get 64 = row) (load : LoadOk m (sp+24) 8)
    (digits : memLoad m (sp+24) 64 = row + 1920) :
    ∃ b : Registers, Reaches .l11034e a m .l110366 b m ∧
      b[1] = ⟨64,BitVec.ofNat 64 i⟩ ∧ b[2] = ⟨64,row + 1920⟩ ∧
      b[6] = ⟨64,row + BitVec.ofNat 64 (960*i)⟩ ∧
      b[12] = ⟨64,BitVec.ofNat 64 (i+1)⟩ ∧ b[15].width = 64 ∧
      ∀ r : Fin Reg.count, r.val ∈ [3,4,5,8,9,13,14,22,39,50,51] → b[r] = a[r] := by
  refine ⟨?_,jump ?run,?post⟩
  case run =>
    cfg_eval [rsp,component,base,load,digits]
    rfl
  case post =>
    refine ⟨rfl,rfl,?_,?_,rfl,?_⟩
    · change Value.mk 64 (BitVec.ofNat 64 i * 960 + row) = _
      rw [Nat.mul_comm,BitVec.ofNat_mul, BitVec.add_comm]
      rfl
    · rw [BitVec.ofNat_add]
      rfl
    · rintro ⟨r,hr⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem chooseJump (d : Int) (regs : Registers) (m : Ram) :
    (if (!decide (d = 0)) = true then Transfer.jump ⟨.l1103c0, regs, m⟩
      else Transfer.jump ⟨.l11037b, regs, m⟩) =
      (Transfer.jump ⟨if d = 0 then .l11037b else .l1103c0, regs, m⟩ :
        Transfer Value Ram Label signature Reg.count) := by
  by_cases h : d = 0 <;> simp [h]

private theorem lookupByte {a : Registers} {m : Ram} {hdr : BitVec 64} {i k : Nat} {d : Int}
    (rcx : a[1].get 64 = BitVec.ofNat 64 i) (rdx : a[2].get 64 = hdr)
    (counter : a[9].get 64 = BitVec.ofNat 64 k)
    (load : LoadOk m (hdr + BitVec.ofNat 64 (272*i) + 8 + BitVec.ofNat 64 k) 1)
    (digit : memLoad m (hdr + BitVec.ofNat 64 (272*i) + 8 + BitVec.ofNat 64 k) 8 = BitVec.ofInt 8 d)
    (valid : Naf.ValidDigit d) :
    ∃ b : Registers, Reaches .l110366 a m (if d = 0 then .l11037b else .l1103c0) b m ∧
      b[1].width = 64 ∧ b[7] = ⟨64,(BitVec.ofInt 8 d).setWidth 64⟩ ∧
      ∀ r : Fin Reg.count, r.val ∈ [2,3,4,5,6,8,9,12,13,14,15,22,39,50,51] → b[r] = a[r] := by
  have ea : BitVec.ofNat 64 k + (BitVec.ofNat 64 i * 272 + hdr) + 8 =
      hdr + BitVec.ofNat 64 (272*i) + 8 + BitVec.ofNat 64 k := by
    rw [BitVec.ofNat_mul,BitVec.mul_comm]
    bv_omega
  have zero : ((BitVec.ofInt 8 d).setWidth 64 == 0) = decide (d = 0) := by
    rcases valid with rfl | ⟨_,lo,hi⟩
    · rfl
    · obtain ⟨x,rfl⟩ : ∃ x : Fin 31, d = (x.val : Int) - 15 := ⟨⟨(d+15).toNat,by omega⟩,by simp only; omega⟩
      exact (by decide +kernel : ∀ x : Fin 31, ((BitVec.ofInt 8 ((x.val : Int)-15)).setWidth 64 == 0) =
        decide (((x.val : Int)-15) = 0)) x
  refine ⟨?_,jump ?run,?post⟩
  case run =>
    cfg_eval [rcx,rdx,counter,ea,load,digit,BitVec.and_self,testFlags,zero]
    rw [ea,ite_eq_left load,digit,zero,chooseJump]
  case post =>
    refine ⟨rfl,rfl,?_⟩
    rintro ⟨r,hr⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem lookupDigit {a b : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {k : Nat} {value : Curve.Point} {d : Int} (j : Fin 4)
    (state : Column a m sp dst table k value b n) (cursor : Cursor sp table j (j.val%2) b n)
    (header : LoadOk n (baseSp sp + 24) 8)
    (load : LoadOk n (row table j + 1920 + BitVec.ofNat 64 (272*(j.val%2)) + 8 + BitVec.ofNat 64 k) 1)
    (digit : memLoad n (row table j + 1920 + BitVec.ofNat 64 (272*(j.val%2)) + 8 + BitVec.ofNat 64 k) 8 =
      BitVec.ofInt 8 d) (valid : Naf.ValidDigit d) :
    ∃ c : Registers, Reaches .l11034e b n (if d = 0 then .l11037b else .l1103c0) c n ∧
      Column a m sp dst table k value c n ∧ Cursor sp table j (j.val%2+1) c n ∧
      c[6].get 64 = row table j + BitVec.ofNat 64 (960*(j.val%2)) ∧
      c[7] = ⟨64,(BitVec.ofInt 8 d).setWidth 64⟩ ∧ c[15].width = 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → c[i].width = 64) := by
  obtain ⟨t,step,one,two,six,idx,fifteen,kept⟩ := lookupRow
    (congrArg (Value.get 64) state.rsp) (congrArg (Value.get 64) cursor.component)
    (congrArg (Value.get 64) cursor.base) header cursor.digits
  obtain ⟨c,run,wone,byte,keep⟩ := lookupByte (congrArg (Value.get 64) one)
    (congrArg (Value.get 64) two) (congrArg (Value.get 64) ((kept 9 (by decide)).trans state.counter))
    load digit valid
  have both (i : Fin Reg.count) (hi : i.val ∈ [3,4,5,8,9,13,14,22,39,50,51]) :=
    (keep i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [3,4,5,8,9,13,14,22,39,50,51] →
      i.val ∈ [2,3,4,5,6,8,9,12,13,14,15,22,39,50,51]) i hi)).trans (kept i hi)
  refine ⟨c,step.trans run,state.withRegs (fun i hi => both i ((by decide : ∀ i : Fin Reg.count,
    i.val ∈ [4,5,8,9,22,39,50,51] → i.val ∈ [3,4,5,8,9,13,14,22,39,50,51]) i hi)),
    ⟨(both 3 (by decide)).trans cursor.count,(keep 12 (by decide)).trans idx,
      (both 13 (by decide)).trans cursor.base,(both 14 (by decide)).trans cursor.next,cursor.digits⟩,
    congrArg (Value.get 64) ((keep 6 (by decide)).trans six),byte,
    (congrArg Value.width (keep 15 (by decide))).trans fifteen,?_⟩
  rintro ⟨i,hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact wone
  · exact congrArg Value.width ((keep 2 (by decide)).trans two)
  · exact congrArg Value.width ((both 8 (by decide)).trans state.back)
  · exact congrArg Value.width ((both 9 (by decide)).trans state.counter)

end K256.Proofs.Verify.Core.Lincomb.Loop
