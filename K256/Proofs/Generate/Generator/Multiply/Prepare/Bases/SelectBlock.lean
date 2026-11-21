import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Selection
namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.DomainParameters.Secp256k1 Common.Point.TableWords

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem dispatchSelect {t : Word} {a : Registers} {m : Ram} {p q : Vector Word 4}
    {first : BitVec 8} (neg : Bool) {x y z : Limbs}
    (rsp : a[4].get 64 = t) (r3 : a[3].get 64 = 0x3ffffffffffffc)
    (r12 : a[12].get 64 = p[0]) (r13 : a[13].get 64 = p[1])
    (r14 : a[14].get 64 = p[2]) (r5 : a[5].get 64 = p[3])
    (zero : memLoad m (t+8) 64 = 0)
    (pair₁ : memLoad m (t+0x38) 64 = t+7112)
    (pair₂ : memLoad m (t+0xb0) 64 = t+7112)
    (s₁ : memLoad m (t+0x30) 8 = first)
    (s₂ : memLoad m (t+0x48) 8 = if neg then 1 else 0)
    (args : WordsAt m (t+0x128) 64 q)
    (px : WordsAt m (t+7112) 64 x) (py : WordsAt m (t+7152) 64 y)
    (pz : WordsAt m (t+7192) 64 z)
    (stack : Writable Extracted.programImage m (t-8) 0x440)
    (src : Readable m (t+7112) 120) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l11ccfd,a,m⟩ =
      .call ⟨.l10fcc0,b,memStore (stageSelect m t (if neg then 1 else 0) (if neg then q else p) x y z)
        (t-8) (0x11cf0d : Word)⟩ (callFrame .l11cf0d 0x11cf0d) ∧
      b[4] = ⟨64,t-8⟩ ∧ b[7] = ⟨64,t+0x328⟩ ∧ b[6] = ⟨64,t+7112⟩ ∧
      b[2] = ⟨64,t+0x3a0⟩ ∧ (b[1].get 64).setWidth 8 = first ∧
      b[5] = ⟨64,t+0x328⟩ ∧ b[3] = a[3] ∧ b[12] = ⟨64,0xfffffffffffff⟩ ∧
      b[14] = ⟨64,0xffffffffffff⟩ ∧ b[15] = a[15] ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i] := by
  have q0 : memLoad m (t+296) 64 = q[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using args 0 (by decide)
  have q1 : memLoad m (t+304) 64 = q[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using args 1 (by decide)
  have q2 : memLoad m (t+312) 64 = q[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using args 2 (by decide)
  have q3 : memLoad m (t+320) 64 = q[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using args 3 (by decide)
  have x0 : memLoad m (t+7112) 64 = x[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using px 0 (by decide)
  have x1 : memLoad m (t+7120) 64 = x[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using px 1 (by decide)
  have x2 : memLoad m (t+7128) 64 = x[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using px 2 (by decide)
  have x3 : memLoad m (t+7136) 64 = x[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using px 3 (by decide)
  have x4 : memLoad m (t+7144) 64 = x[4] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using px 4 (by decide)
  have y0 : memLoad m (t+7152) 64 = y[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using py 0 (by decide)
  have y1 : memLoad m (t+7160) 64 = y[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using py 1 (by decide)
  have y2 : memLoad m (t+7168) 64 = y[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using py 2 (by decide)
  have y3 : memLoad m (t+7176) 64 = y[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using py 3 (by decide)
  have y4 : memLoad m (t+7184) 64 = y[4] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using py 4 (by decide)
  have z0 : memLoad m (t+7192) 64 = z[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using pz 0 (by decide)
  have z1 : memLoad m (t+7200) 64 = z[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using pz 1 (by decide)
  have z2 : memLoad m (t+7208) 64 = z[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using pz 2 (by decide)
  have z3 : memLoad m (t+7216) 64 = z[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using pz 3 (by decide)
  have z4 : memLoad m (t+7224) 64 = z[4] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset, BitVec.reduceAdd, BitVec.add_zero] using pz 4 (by decide)
  cases neg
  case false =>
    refine ⟨?_, ?runfalse, ?restfalse⟩
    case runfalse =>
      arithmetic_segment using code_l11ccfd [rsp,r3,r12,r13,r14,r5,zero,pair₁,pair₂,s₁,s₂,
        stageSelect,BitVec.add_zero,BitVec.zero_add,Lift.reduceAddOffset,BitVec.reduceAdd,
        q0, q1, q2, q3, x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, z0, z1, z2, z3, z4]
    case restfalse =>
      refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
      · simp [Value.get]
      · rintro ⟨i,hi⟩ hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl|rfl|rfl|rfl <;> rfl
  case true =>
    refine ⟨?_, ?runtrue, ?resttrue⟩
    case runtrue =>
      arithmetic_segment using code_l11ccfd [rsp,r3,r12,r13,r14,r5,zero,pair₁,pair₂,s₁,s₂,
        stageSelect,BitVec.add_zero,BitVec.zero_add,Lift.reduceAddOffset,BitVec.reduceAdd,
        q0, q1, q2, q3, x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, z0, z1, z2, z3, z4]
    case resttrue =>
      refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
      · simp [Value.get]
      · rintro ⟨i,hi⟩ hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
