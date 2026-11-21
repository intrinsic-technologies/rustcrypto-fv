import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Negate

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Sec1.Affine.Uncompressed

def storeFour (m : Ram) (base : BitVec 64) (w : Vector (BitVec 64) 4) : Ram :=
  memStore (memStore (memStore (memStore m base w[0]) (base + 8) w[1]) (base + 16) w[2]) (base + 24) w[3]

def selectFour (s : BitVec 8) (a b : Vector (BitVec 64) 4) : Vector (BitVec 64) 4 :=
  Vector.ofFn fun i => if s = 0 then a[i] else b[i]

def selectedMemory (m : Ram) (base : BitVec 64) (sign : BitVec 8)
    (raw negated : Vector (BitVec 64) 4) : Ram :=
  storeFour (memStore m (base + 0x1d0) sign) (base + 0x270) (selectFour sign raw negated)

theorem wordLoads {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    (h : WordsAt m (base + 0x418) 64 w) :
    memLoad m (base + 0x418) 64 = w[0] ∧ memLoad m (base + 0x420) 64 = w[1] ∧
    memLoad m (base + 0x428) 64 = w[2] ∧ memLoad m (base + 0x430) 64 = w[3] := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [wordAddr, Nat.reduceMul, Nat.reduceDiv, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 950000 in
theorem selectPrefix {a : Registers} {m : Ram} {base : BitVec 64} {sgn : BitVec 8}
    {raw negated : Vector (BitVec 64) 4}
    (win : Writable Extracted.programImage m base 3256)
    (sp : a[4].get 64 = base)
    (r3 : a[3].get 64 = raw[0]) (r13 : a[13].get 64 = raw[1])
    (r14 : a[14].get 64 = raw[2]) (r12 : a[12].get 64 = raw[3])
    (sign : memLoad m (base + 0x30) 8 = sgn)
    (neg : WordsAt m (base + 0x418) 64 negated) :
    ∃ b : Values Value 88,
      b_l11cc3e.eval (dialect Extracted.programImage) a m =
        b_l11cc3e_1.eval (dialect Extracted.programImage) b (selectedMemory m base sgn raw negated) ∧
      a.Prefix b ∧ b[84] = ⟨64,0x3ffffffffffffc⟩ ∧ b[76].width = 64 := by
  obtain ⟨n0,n1,n2,n3⟩ := wordLoads neg
  refine ⟨?b,?ev,?pre,?mask,?cx⟩
  case ev =>
    simp only [selectedMemory,storeFour,selectFour,Vector.getElem_ofFn,BitVec.add_assoc,BitVec.reduceAdd]
    arithmetic_prefix [sp,r3,r13,r14,r12,sign,n0,n1,n2,n3,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq,BitVec.and_self,ite_not]
    segment_words [sign,n0,n1,n2,n3,ite_not]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l11cc3e)
    rfl
  case pre =>
    repeat' apply Values.Prefix.push
    exact Values.Prefix.refl _
  case mask => simp only [↓arithmeticRead]
  case cx => simp only [↓arithmeticRead]

def dispatchMemory (m : Ram) (base : BitVec 64) (v : Vector (BitVec 64) 4) : Ram :=
  memStore (storeFour m (base + 0x1d0) v) (base - 8) (0x11ccfd : BitVec 64)

structure Dispatched (a b : Registers) (base : BitVec 64) (v : Vector (BitVec 64) 4) : Prop where
  widths : ParseSignature.ArgumentWidths b
  rsp : b[4] = ⟨64,base - 8⟩
  rsi : b[6].get 64 = base + 0x1d0
  rdi : b[7].get 64 = base + 0x128
  rdx : b[2].get 64 = 0x2021a0
  rbp : b[5] = a[5]
  work : b[15] = a[15]
  mask : b[3] = ⟨64,0x3ffffffffffffc⟩
  v0 : b[12] = ⟨64,v[0]⟩
  v1 : b[13] = ⟨64,v[1]⟩
  v2 : b[14] = ⟨64,v[2]⟩
  keep : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
theorem dispatchTail {original : Registers} {a : Values Value 88} {m : Ram} {base : BitVec 64}
    {v : Vector (BitVec 64) 4}
    (win : Writable Extracted.programImage m base 3256)
    (below : Writable Extracted.programImage m (base-8) 8)
    (pre : original.Prefix a) (widths : ParseSignature.ArgumentWidths original)
    (sp : a[4].get 64 = base)
    (w3 : a[5].get 64 = v[3])
    (src : a[15].get 64 = base + 0x1d0)
    (mask : a[84] = ⟨64,0x3ffffffffffffc⟩) (cx : a[76].width = 64)
    (w0 : memLoad m (base + 0xa8) 64 = v[0])
    (w1 : memLoad m (base + 0x40) 64 = v[1])
    (w2 : memLoad m (base + 0x10) 64 = v[2]) :
    ∃ b : Registers,
      b_l11cc3e_1.eval (dialect Extracted.programImage) a m =
        .call ⟨.l110b80,b,dispatchMemory m base v⟩ (callFrame .l11ccfd 0x11ccfd) ∧
      Dispatched original b base v := by
  have p8 := pre.2 8 (by decide) (by decide)
  have p9 := pre.2 9 (by decide) (by decide)
  refine ⟨?b,?ev,⟨?widths,?rsp,?si,?di,?dx,?bp,?work,?r3,?v0,?v1,?v2,?ctrl⟩⟩
  case ev =>
    simp only [dispatchMemory,storeFour,BitVec.add_assoc,BitVec.reduceAdd]
    simp only [cfg_eval, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSignExtend,
      BitVec.reduceSetWidth, sp,w3,src]
    segment_words [w0,w1,w2]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l11cc3e_1)
    rfl
  case widths =>
    intro ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | rfl
      | exact cx
      | have old := widths 8 (by decide); exact (congrArg Value.width p8).trans old
      | have old := widths 9 (by decide); exact (congrArg Value.width p9).trans old
  case bp => exact pre.2 5 (by decide) (by decide)
  case work => exact pre.2 15 (by decide) (by decide)
  case r3 => exact mask
  case ctrl =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> exact pre.2 _ (by decide) (by decide)
  all_goals rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Negate
