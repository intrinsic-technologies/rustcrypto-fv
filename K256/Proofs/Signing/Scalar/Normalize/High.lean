import K256.Proofs.Signing.Scalar.Normalize.State
import K256.Proofs.Verify.LIR.Fn104c90
import K256.Proofs.Verify.LIR.Fn1065b0
import K256.Proofs.Verify.LIR.Functions1
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Scalar.Normalize

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Verify.LIR Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

private abbrev Registers := Verify.Core.Registers
private abbrev highKept : List Nat := [3,5,13,14,22,39,50,51]
private abbrev keeps (a b : Registers) (rs : List Nat) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ rs → b[i] = a[i]

local macro "kept_regs" : tactic => `(tactic|
  (rintro ⟨i,_⟩ h
   simp only [highKept,List.mem_cons,List.not_mem_nil,or_false] at h
   first
   | (rcases h with h | h | h | h | h | h | h | h <;> subst i <;> rfl)
   | (rcases h with h | h | h | h | h | h | h <;> subst i <;> rfl)
   | (rcases h with h | h | h | h | h | h <;> subst i <;> rfl)
   | (rcases h with h | h | h | h <;> subst i <;> rfl)))

local macro "compare_block" cd:term:max " with " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (cfg_eval [$hs,*]
     segment_words [$hs,*]
     repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using $cd | assumption)
     try rfl))

private theorem comparePush {a : Registers} {m : Ram} {base src : BitVec 64}
    (stack : Writable Extracted.programImage m base 176)
    (sp : a[4].get 64 = base + 176) (ptr : a[15].get 64 = src) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l104d56,a,m⟩ =
        .call ⟨.l108380,b,n⟩ (Verify.resumeAt .l104d5e 0x104d5e) ∧
      b[4] = ⟨64,base+168⟩ ∧ b[7] = ⟨64,src⟩ ∧ keeps a b highKept ∧
      memLoad n (base+168) 64 = 0x104d5e ∧ RamWriteFrame m n [⟨base.toNat,176⟩] := by
  have lim := stack.readable.low
  refine ⟨?_,?_,?run,?_,?_,?keep,?_,?_⟩
  case run => compare_block code_l104d56 with [sp,ptr]
  case keep => kept_regs
  all_goals first | slot_state region | (segment_words [] <;> rfl)

private abbrev orderHalf : Vector (BitVec 64) 4 :=
  #v[0xdfe92f46681b20a0,0x5d576e7357a4501d,0xffffffffffffffff,0x7fffffffffffffff]

set_option maxHeartbeats 900000 in
private theorem halfOrderCall {a : Registers} {m : Ram} {base src : BitVec 64}
    (stack : Writable Extracted.programImage m base 176)
    (sp : a[4].get 64 = base + 168) (ptr : a[7].get 64 = src) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l108380,a,m⟩ =
        .call ⟨.l1065b0,b,n⟩ (Verify.resumeAt .l1083d3 0x1083d3) ∧
      b[4] = ⟨64,base+72⟩ ∧ b[7] = ⟨64,base+96⟩ ∧ b[6] = ⟨64,base+128⟩ ∧
      b[2] = ⟨64,1⟩ ∧ b[3] = ⟨64,src⟩ ∧ keeps a b [5,13,14,22,39,50,51] ∧
      memLoad n (base+160) 64 = a[3].get 64 ∧
      memLoad n (base+72) 64 = 0x1083d3 ∧
      memLoad n (base+168) 64 = memLoad m (base+168) 64 ∧
      RamWriteFrame m n [⟨base.toNat,176⟩] ∧
      memLoad n (base+128) 64 = 0xbfd25e8cd0364141 ∧
      memLoad n (base+136) 64 = 0xbaaedce6af48a03b ∧
      memLoad n (base+144) 64 = 0xfffffffffffffffe ∧
      memLoad n (base+152) 64 = 0xffffffffffffffff := by
  have lim := stack.readable.low
  refine ⟨?_,?_,?run,?_,?_,?_,?_,?_,?keep,?_,?_,?_,?_,?_,?_,?_,?_⟩
  case run => compare_block code_l108380 with [sp,ptr]
  case keep => kept_regs
  all_goals first | slot_state region | (segment_words [] <;> rfl)

set_option maxHeartbeats 900000 in
private theorem shiftEnter {a : Registers} {m : Ram} {base : BitVec 64}
    (stack : Writable Extracted.programImage m base 176)
    (sp : a[4].get 64 = base + 72) (shift : a[2].get 64 = 1) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l1065b0,a,m⟩ = .jump ⟨.l1065ca,b,n⟩ ∧
      b[4] = ⟨64,base⟩ ∧ keeps a b [2,6,7,22,39,50,51] ∧
      memLoad n (base+24) 64 = a[3].get 64 ∧ memLoad n (base+32) 64 = a[12].get 64 ∧
      memLoad n (base+40) 64 = a[13].get 64 ∧ memLoad n (base+48) 64 = a[14].get 64 ∧
      memLoad n (base+56) 64 = a[15].get 64 ∧ memLoad n (base+64) 64 = a[5].get 64 ∧
      memLoad n (base+72) 64 = memLoad m (base+72) 64 ∧
      memLoad n (base+128) 64 = memLoad m (base+128) 64 ∧
      memLoad n (base+136) 64 = memLoad m (base+136) 64 ∧
      memLoad n (base+144) 64 = memLoad m (base+144) 64 ∧
      memLoad n (base+152) 64 = memLoad m (base+152) 64 ∧
      memLoad n (base+160) 64 = memLoad m (base+160) 64 ∧
      memLoad n (base+168) 64 = memLoad m (base+168) 64 ∧
      RamWriteFrame m n [⟨base.toNat,176⟩] := by
  have lim := stack.readable.low
  have cmp : (cmpSpec (1 : BitVec 32) 256).CF = true := by decide
  refine ⟨?_,?_,?run,?_,?keep,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  case run => compare_block code_l1065b0 with [sp,shift,cmp]
  case keep => kept_regs
  all_goals first | slot_state region | (segment_words [] <;> rfl)

private theorem stepJump {l l' : Label} {a b : Registers} {m n : Ram}
    (jump : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨l',b,n⟩) :
    program.step (dialect Extracted.programImage) ⟨⟨l,a,m⟩,[]⟩ =
      .next ⟨⟨l',b,n⟩,[]⟩ := by
  change (program.runBlock _ _).next _ [] = _
  rw [jump]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem shiftHalf {a : Registers} {m : Ram} {base : BitVec 64}
    (stack : Writable Extracted.programImage m base 176)
    (sp : a[4].get 64 = base + 72) (shift : a[2].get 64 = 1)
    (src : a[6].get 64 = base+128) (dst : a[7].get 64 = base+96)
    (ret : memLoad m (base+72) 64 = 0x1083d3)
    (n0 : memLoad m (base+128) 64 = 0xbfd25e8cd0364141)
    (n1 : memLoad m (base+136) 64 = 0xbaaedce6af48a03b)
    (n2 : memLoad m (base+144) 64 = 0xfffffffffffffffe)
    (n3 : memLoad m (base+152) 64 = 0xffffffffffffffff) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1065b0,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x1083d3⟩ ∧ out.values[4] = ⟨64,base+80⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,13,14] → out.values[i] = ⟨64,a[i].get 64⟩) ∧
      keeps a out.values [22,39,50,51] ∧
      RamWriteFrame m out.store [⟨base.toNat,176⟩] ∧
      WordsAt out.store (base+96) 64 orderHalf ∧
      memLoad out.store (base+160) 64 = memLoad m (base+160) 64 ∧
      memLoad out.store (base+168) 64 = memLoad m (base+168) 64 := by
  obtain ⟨b,n,entry,bsp,keep,rbx,r12,r13,r14,r15,rbp,returnAt,w0,w1,w2,w3,oldBx,oldRet,writes⟩ :=
    shiftEnter stack sp shift
  have bsrc : b[6].get 64 = base+128 := (congrArg (Value.get 64) (keep 6 (by decide))).trans src
  have bdst : b[7].get 64 = base+96 := (congrArg (Value.get 64) (keep 7 (by decide))).trans dst
  have bshift : b[2].get 64 = 1 := (congrArg (Value.get 64) (keep 2 (by decide))).trans shift
  have rsp : b[4].get 64 = base := congrArg (Value.get 64) bsp
  have h0 := w0.trans n0
  have h1 := w1.trans n1
  have h2 := w2.trans n2
  have h3 := w3.trans n3
  have retAt := returnAt.trans ret
  have area := stack.of_frame writes
  have lim := area.readable.low
  have tail : ∃ (c : Registers) (p : Ram) (out : Output Value Ram Reg.count),
      program.runBlock (dialect Extracted.programImage) ⟨.l1065ca,b,n⟩ = .jump ⟨.l106667,c,p⟩ ∧
      program.runBlock (dialect Extracted.programImage) ⟨.l106667,c,p⟩ = .returned out ∧
      out.tag = some ⟨64,0x1083d3⟩ ∧ out.values[4] = ⟨64,base+80⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,13,14] → out.values[i] = ⟨64,a[i].get 64⟩) ∧
      keeps b out.values [22,39,50,51] ∧
      RamWriteFrame n out.store [⟨base.toNat,176⟩] ∧
      WordsAt out.store (base+96) 64 orderHalf ∧
      memLoad out.store (base+160) 64 = memLoad n (base+160) 64 ∧
      memLoad out.store (base+168) 64 = memLoad n (base+168) 64 := by
    refine ⟨?_,?_,?_,?mask,?done,?tag,?sp,?restore,?keep,?frame,?words,?bx,?ret⟩
    case mask =>
      have nz : (andFlags (1 : BitVec 32)).ZF.getD false = false := by decide
      compare_block code_l1065ca with [rsp,bsrc,bdst,bshift,h0,h1,h2,h3,
        BitVec.reduceUShiftRight,BitVec.reduceAnd,setWidth_mergeGPR8,nz]
    case done =>
      cfg_eval [rsp]
      segment_words [rbx,r12,r13,r14,r15,rbp,retAt,BitVec.add_assoc,BitVec.reduceAdd,
        BitVec.reduceAnd,BitVec.reduceNeg,BitVec.reduceUShiftRight,setWidth_mergeGPR8,
        BitVec.reduceSetWidth,BitVec.zero_and,BitVec.zero_xor,BitVec.reduceXOr]
      have code : ∀ x ∈ codeRange 0x106667 bytes_l106667, x ∈ Extracted.programImage :=
        fun x hx => Verify.Core.Affine.coreText x (code_l106667 x hx)
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code | assumption)
      refine Eq.trans (ite_eq_left ⟨by slot_guard using code, by decide⟩) ?_
      rfl
    case restore => kept_regs
    case keep => kept_regs
    case frame =>
      dsimp only [Output.store]
      slot_state region
    case words =>
      intro i hi
      obtain rfl|rfl|rfl|rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
      all_goals
        segment_words [wordAddr, Nat.reduceDiv,Nat.reduceMul,BitVec.reduceOfNat,
          BitVec.add_assoc,BitVec.reduceAdd,setWidth_mergeGPR8]
        first | rfl | decide +kernel
    all_goals (segment_words [] <;> rfl)
  obtain ⟨c,p,out,mask,done,tag,osp,rest,kept,frame,words,bx,retAt⟩ := tail
  refine ⟨out,.next (stepJump entry) (.next (stepJump mask) (.done ?_)),tag,osp,rest,
    fun i h => (kept i h).trans (keep i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      omega)),writes.trans frame (fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩),
    words,bx.trans oldBx,retAt.trans oldRet⟩
  simp only [Program.step,done,Transfer.next]


open Common.Invert.LinearCombination (borrow subRaw subWord Limbs)

private def halfLimbs : Limbs :=
  ⟨0xdfe92f46681b20a0, 0x5d576e7357a4501d, 0xffffffffffffffff, 0x7fffffffffffffff⟩

private def compareBit (w : Vector (BitVec 64) 4) : BitVec 64 :=
  (subRaw halfLimbs ⟨w[0],w[1],w[2],w[3]⟩).2

private theorem compareBit_scalar {s : Nat} (hs : s < domain.n) :
    compareBit (scalarWords s) = if domain.n / 2 < s then 1 else 0 := by
  let w := scalarWords s
  let limbs : Limbs := ⟨w[0],w[1],w[2],w[3]⟩
  have bound : s < 2^256 := Nat.lt_trans hs (by decide +kernel)
  have value : limbs.toNat = s := Split.scalarWords_value s bound
  have half : halfLimbs.toNat = domain.n / 2 := by decide +kernel
  have h := Common.Invert.LinearCombination.subRaw_toNat halfLimbs limbs
  have lo := (subRaw halfLimbs limbs).1.l0.isLt
  have mid := (subRaw halfLimbs limbs).1.l1.isLt
  have hi := (subRaw halfLimbs limbs).1.l2.isLt
  have top := (subRaw halfLimbs limbs).1.l3.isLt
  have rem : (subRaw halfLimbs limbs).1.toNat < 2^256 := by
    unfold Limbs.toNat
    omega
  rw [half,value] at h
  change (subRaw halfLimbs limbs).2 = _
  split <;> apply BitVec.eq_of_toNat_eq
  · change (subRaw halfLimbs limbs).2.toNat = 1
    omega
  · change (subRaw halfLimbs limbs).2.toNat = 0
    omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
private theorem compareCall {a : Registers} {m : Ram} {base src : BitVec 64}
    {w : Vector (BitVec 64) 4} (stack : Writable Extracted.programImage m base 176)
    (read : Readable m src 32) (separate : base.toNat + 176 ≤ src.toNat)
    (sp : a[4].get 64 = base + 80) (ptr : a[3].get 64 = src)
    (half : WordsAt m (base+96) 64 orderHalf) (words : WordsAt m src 64 w) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l1083d3,a,m⟩ =
        .call ⟨.l127d50,b,memStore n (base+72) (0x1084af : BitVec 64)⟩
          (Verify.resumeAt .l1084af 0x1084af) ∧
      b[4] = ⟨64,base+72⟩ ∧ b[7] = ⟨64, (compareBit w).setWidth 8 |>.setWidth 64⟩ ∧
      keeps a b [5,13,14,22,39,50,51] ∧
      RamWriteFrame m n [⟨base.toNat,176⟩] ∧
      memLoad n (base+160) 64 = memLoad m (base+160) 64 ∧
      memLoad n (base+168) 64 = memLoad m (base+168) 64 := by
  have lim := stack.readable.low
  have rlo := read.low
  have h0 := half 0 (by decide)
  change memLoad m (wordAddr (base+96) 64 0) 64 = (0xdfe92f46681b20a0 : BitVec 64) at h0
  simp only [wordAddr, Nat.reduceDiv,Nat.reduceMul,BitVec.add_zero] at h0
  have h1 := half 1 (by decide)
  change memLoad m (wordAddr (base+96) 64 1) 64 = (0x5d576e7357a4501d : BitVec 64) at h1
  simp only [wordAddr, Nat.reduceDiv,Nat.reduceMul,Lift.reduceAddOffset] at h1
  have h2 := half 2 (by decide)
  change memLoad m (wordAddr (base+96) 64 2) 64 = (0xffffffffffffffff : BitVec 64) at h2
  simp only [wordAddr, Nat.reduceDiv,Nat.reduceMul,Lift.reduceAddOffset] at h2
  have h3 := half 3 (by decide)
  change memLoad m (wordAddr (base+96) 64 3) 64 = (0x7fffffffffffffff : BitVec 64) at h3
  simp only [wordAddr, Nat.reduceDiv,Nat.reduceMul,Lift.reduceAddOffset] at h3
  have w0 : memLoad m src 64 = w[0] := by
    simpa only [wordAddr, Nat.reduceDiv,Nat.reduceMul,BitVec.add_zero,Lift.reduceAddOffset] using words 0 (by decide)
  have w1 : memLoad m (src+8) 64 = w[1] := words 1 (by decide)
  have w2 : memLoad m (src+16) 64 = w[2] := words 2 (by decide)
  have w3 : memLoad m (src+24) 64 = w[3] := words 3 (by decide)
  refine ⟨?_,?_,?run,?sp,?flag,?keep,?frame,?bx,?ret⟩
  case run => compare_block code_l1083d3 with [sp,ptr,h0,h1,h2,h3,w0,w1,w2,w3]
  case sp => rfl
  case flag =>
    have hb : (compareBit w).toNat ≤ 1 :=
      (Common.Invert.LinearCombination.subRaw_toNat halfLimbs ⟨w[0],w[1],w[2],w[3]⟩).1
    have flagValue (v : BitVec 64) (hv : v.toNat ≤ 1) :
        (⟨64, (mergeGPR 8 (v.extractLsb' 0 8 &&& 1) ((v.extractLsb' 0 8).setWidth 64)).setWidth 8
          |>.setWidth 64⟩ : Value) = ⟨64,(v.setWidth 8).setWidth 64⟩ := by
      rcases Common.Invert.LinearCombination.eq_zero_or_one hv with h | h <;> rw [h] <;> rfl
    change (⟨64, (mergeGPR 8 (_ &&& 1) _).setWidth 8 |>.setWidth 64⟩ : Value) = _
    have zeroSub (x : BitVec 64) : (0 : BitVec 64) - x = -x := BitVec.zero_sub x
    have minusOne (x y : BitVec 64) : x - 1 - y = x + (0xffffffffffffffff - y) := by bv_omega
    have rearrange (x y z : BitVec 64) : x + y - z = x + (y - z) := by bv_omega
    simp only [zeroSub,minusOne,rearrange]
    have c0 : ~~~(0xdfe92f46681b20a0 : BitVec 64) = 2312264954237214559 := rfl
    have c1 : ~~~(0x5d576e7357a4501d : BitVec 64) = 11720778063537745890#64 := rfl
    have c2 : ~~~(0xffffffffffffffff : BitVec 64) = 0#64 := rfl
    have c3 : ~~~(0x7fffffffffffffff : BitVec 64) = 9223372036854775808#64 := rfl
    have h := flagValue (compareBit w) hb
    simp only [compareBit,halfLimbs,subRaw,subWord,borrow,c0,c1,c2,c3] at h
    exact h
  case keep => kept_regs
  case frame => slot_state region
  case bx => segment_words []
  case ret => segment_words []

private theorem compareReturn {a : Registers} {m : Ram} {base rbx : BitVec 64}
    (stack : Writable Extracted.programImage m base 176) (sp : a[4].get 64 = base+80)
    (saved : memLoad m (base+160) 64 = rbx)
    (ret : memLoad m (base+168) 64 = 0x104d5e) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1084af,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x104d5e⟩ ∧ out.values[4] = ⟨64,base+176⟩ ∧
      out.values[3] = ⟨64,rbx⟩ ∧ out.values[0] = a[0] ∧
      keeps a out.values [5,13,14,22,39,50,51] ∧ out.store = m := by
  have lim := stack.readable.low
  suffices ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l1084af,a,m⟩ =
      .returned out ∧ out.tag = some ⟨64,0x104d5e⟩ ∧ out.values[4] = ⟨64,base+176⟩ ∧
      out.values[3] = ⟨64,rbx⟩ ∧ out.values[0] = a[0] ∧
      keeps a out.values [5,13,14,22,39,50,51] ∧ out.store = m by
    obtain ⟨out,run,post⟩ := this
    exact ⟨out,.done (by simp only [Program.step,run,Transfer.next]),post⟩
  refine ⟨?_,?run,?tag,?sp,?bx,?flag,?keep,?mem⟩
  case run =>
    have rb := stack.readable.of_offsets (n := 8) (show base+160 = base+160 from rfl) (addr_self base) (by decide)
    have rt := stack.readable.of_offsets (n := 8) (show base+168 = base+168 from rfl) (addr_self base) (by decide)
    have pop : LoadOk m (base+160) 8 := ⟨rb.low,rb.present⟩
    have retSlot : LoadOk m (base+168) 8 := ⟨rt.low,rt.present⟩
    cfg_eval [sp,saved,ret,BitVec.add_assoc,BitVec.reduceAdd,pop,retSlot]
    rfl
  case keep => kept_regs
  all_goals rfl

private theorem choiceAndReturn {base : BitVec 64} {a b : Registers} {m pre : Ram}
    {w : Vector (BitVec 64) 4} (stack : Writable Extracted.programImage m base 176)
    (branch : program.runBlock (dialect Extracted.programImage) ⟨.l1083d3,a,m⟩ =
      .call ⟨.l127d50,b,memStore pre (base+72) (0x1084af : BitVec 64)⟩
        (Verify.resumeAt .l1084af 0x1084af))
    (sp : b[4] = ⟨64,base+72⟩) (flag : b[7] = ⟨64,(compareBit w).setWidth 8 |>.setWidth 64⟩)
    (frame : RamWriteFrame m pre [⟨base.toNat,176⟩])
    {rbx : BitVec 64} (saved : memLoad pre (base+160) 64 = rbx)
    (ret : memLoad pre (base+168) 64 = 0x104d5e) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1083d3,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x104d5e⟩ ∧ out.values[4] = ⟨64,base+176⟩ ∧
      out.values[3] = ⟨64,rbx⟩ ∧ out.values[0].get 8 = (compareBit w).setWidth 8 ∧
      keeps b out.values [5,13,14,22,39,50,51] ∧
      RamWriteFrame m out.store [⟨base.toNat,176⟩] := by
  have lim := stack.readable.low
  have area := stack.of_frame frame
  have callSlot : base + 80 - 8 = base + 72 := by bv_omega
  have scratchSlot : base + 80 - 8 - 1 = base + 71 := by bv_omega
  have sp' : b[4].get 64 = base + 80 - 8 := by
    rw [callSlot]
    exact congrArg (Value.get 64) sp
  have temp : Writable Extracted.programImage pre (base+80-8-1) 1 := by
    rw [scratchSlot]
    exact area.of_offsets rfl (addr_self base) (by decide)
  have slot : Readable pre (base+80-8) 8 := by
    rw [callSlot]
    exact area.readable.of_offsets rfl (addr_self base) (by decide)
  have pushed : InRegions [⟨base.toNat,176⟩] (base+72) 8 := by
    refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [InRegion,BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]
    omega
  obtain ⟨c,n,resume,csp,byte,delta,kept⟩ :=
    Verify.resumeChoice (sp := base+80) (by rwa [callSlot]) sp' temp slot (by decide)
  rw [callSlot,show base + 72 - 1 = base + 71 by bv_omega] at delta
  have small (i : BitVec 64) (hi : i.toNat + 8 ≤ 176) :
      (base+i).toNat = base.toNat+i.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have slotNat : (base+71).toNat = base.toNat+71 := small 71 (by decide)
  have savedAt (i : BitVec 64) (lo : 80 ≤ i.toNat) (hi : i.toNat+8 ≤ 176) :
      memLoad n (base+i) 64 = memLoad pre (base+i) 64 := by
    refine (delta.memLoad_eq ?_).trans (memLoad_memStore_of_rangeApart pre _ _ _ _ ?_)
    · refine ⟨?_,fun r hr => ?_⟩
      · rw [small i hi]
        omega
      · obtain rfl := List.mem_singleton.mp hr
        right
        change (base+71).toNat + 1 ≤ (base+i).toNat
        rw [small i hi,slotNat]
        omega
    · apply RangeApart.of_offsets (x := base) rfl rfl
      have iRange := i.isLt
      simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow]
      omega
  have whole : RamWriteFrame m n [⟨base.toNat,176⟩] := by
    apply (frame.memStore (0x1084af : BitVec 64) pushed).trans delta
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;> simp only [slotNat] <;> omega
  obtain ⟨out,exec,tag,osp,obx,o0,okeep,store⟩ := compareReturn (stack.of_frame whole)
    (congrArg (Value.get 64) csp) ((savedAt 160 (by decide) (by decide)).trans saved)
    ((savedAt 168 (by decide) (by decide)).trans ret)
  refine ⟨out,Program.Exec.of_sem (resume.exec exec.sem),tag,osp,obx,?_,?_,store.symm ▸ whole⟩
  · rw [o0,byte,flag]
    simp only [Value.get,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq]
  · intro i hi
    refine (okeep i hi).trans (kept i ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega

set_option maxHeartbeats 700000 in
theorem high {fr : Activation} {a : Verify.Core.Registers} {r s : Nat}
    (input : Inputs fr r s) {m : Ram} (saved : Saved fr a m)
    (ptr : a[15].get 64 = fr.rsi + 32)
    (negated : WordsAt m (fr.rsp - 128) 64 (scalarWords (domain.n - s))) :
    ∃ b n, Verify.Core.Reaches .l104d56 a m .l104d5e b n ∧ Saved fr b n ∧
      b[0].get 8 = (if s > domain.n / 2 then 1 else 0) ∧
      WordsAt n (fr.rsp - 128) 64 (scalarWords (domain.n - s)) := by
  let base := fr.rsp - 312
  let src := fr.rsi + 32
  let work : List MemoryRegion := [⟨base.toNat,176⟩]
  have room := input.room
  have upper := input.high
  have baseNat : base.toNat = fr.rsp.toNat - 312 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show 312 ≤ fr.rsp.toNat by omega))
  have lowNat : fr.low.toNat = fr.rsp.toNat - 464 := by
    rw [input.low]
    exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have srcNat : src.toNat = fr.rsp.toNat + 232 := by
    simp only [src,input.src,BitVec.add_assoc,BitVec.reduceAdd,BitVec.toNat_add,
      BitVec.reduceToNat,Nat.reducePow]
    omega
  have spBase : base + 176 = fr.rsp - 136 := by dsimp only [base]; bv_omega
  have inset : RegionsWithin work [fr.region] := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;>
      simp only [Activation.region,baseNat,lowNat] <;> omega
  have outside {d n : Nat} (after : 136 ≥ d) (len : n ≤ 32) :
      Outside work (fr.rsp - BitVec.ofNat 64 d) n := by
    have off : (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
      have bound : d < 2^64 := by omega
      rw [BitVec.toNat_sub_of_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
      apply BitVec.le_def.mpr
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
      omega
    refine ⟨by rw [off]; omega, fun reg h => ?_⟩
    obtain rfl := List.mem_singleton.mp h
    right
    dsimp only
    rw [off,baseNat]
    omega
  have atoms := saved.atoms
  simp only [Fn104c90.frameAt,Fn104c90.frameAtG5,Atom.All,Atom.Holds] at atoms
  obtain ⟨sp,df,bx,bp,r13,r14,mx,ft,fc,s3,s12,s14,s15,rr,ret,small,stack,stackRoom,alignment,_⟩ := atoms
  have area : Writable Extracted.programImage m base 176 :=
    stack.of_offsets (addr_sub fr.rsp 312) (addr_sub fr.rsp 464) (by decide)
  have read : Readable m src 32 :=
    (input.read.of_frame saved.frame).of_offsets rfl (addr_self fr.rsi) (by decide)
  have spval : a[4].get 64 = base+176 := spBase.symm ▸ congrArg (Value.get 64) sp
  obtain ⟨b,mb,call,bsp,bptr,bkeep,bret,bframe⟩ := comparePush area spval ptr
  obtain ⟨c,mc,shift,csp,cdst,csrc,cone,cbx,ckeep,pushBx,pushRet,retKept,cframe,n0,n1,n2,n3⟩ :=
    halfOrderCall (area.of_frame bframe) (congrArg (Value.get 64) bsp) (congrArg (Value.get 64) bptr)
  obtain ⟨mid,half,htag,hsp,hkeep,hflags,hframe,hwords,saveBx,saveRet⟩ :=
    shiftHalf (area.of_frame (bframe.trans cframe (fun t h => ⟨t,h,Nat.le_refl _,Nat.le_refl _⟩)))
      (congrArg (Value.get 64) csp) (congrArg (Value.get 64) cone)
      (congrArg (Value.get 64) csrc) (congrArg (Value.get 64) cdst) pushRet n0 n1 n2 n3
  have halfReach := Verify.reachesOfCall shift half htag
  have sameRegions : RegionsWithin work work := fun t h => ⟨t,h,Nat.le_refl _,Nat.le_refl _⟩
  have toHalf := (bframe.trans cframe sameRegions).trans hframe sameRegions
  have mptr : mid.values[3].get 64 = src := by
    have reg : mid.values[3] = ⟨64,c[3].get 64⟩ := hkeep 3 (by decide)
    rw [reg,cbx]
    rfl
  obtain ⟨d,md,branch,dsp,dflag,dkeep,dframe,dBx,dRet⟩ :=
    compareCall (area.of_frame toHalf) (read.of_frame toHalf) (by rw [baseNat,srcNat]; omega)
      (congrArg (Value.get 64) hsp) mptr hwords ((input.words_of_frame saved.frame).2.of_frame
        toHalf (by decide) (by
          refine ⟨by rw [srcNat]; omega, fun t h => ?_⟩
          obtain rfl := List.mem_singleton.mp h
          right
          dsimp only
          rw [baseNat,srcNat]
          omega))
  have savedBx : memLoad md (base+160) 64 = fr.rdi := by
    have reg : b[3] = a[3] := bkeep 3 (by decide)
    rw [dBx,saveBx,pushBx]
    exact congrArg (Value.get 64) (reg.trans bx)
  have returnAt := dRet.trans (saveRet.trans (retKept.trans bret))
  obtain ⟨out,tail,tag,outSp,outBx,outFlag,outKeep,delta⟩ :=
    choiceAndReturn (area.of_frame toHalf) branch dsp dflag dframe savedBx returnAt
  have exec : program.Exec (dialect Extracted.programImage) ⟨⟨.l108380,b,mb⟩,[]⟩ out :=
    Program.Exec.of_sem (halfReach.exec tail.sem)
  have finish := Verify.reachesOfCall call exec tag
  have finalFrame := toHalf.trans delta sameRegions
  have keep {i : Fin Reg.count} (hi : i.val ∈ [5,13,14,22,39,50,51])
      (hk : i.val ∈ highKept) : out.values[i] = a[i] := by
    rw [outKeep i hi,dkeep i hi]
    have restored (k : Fin Reg.count) (hs : k.val ∈ [3,5,13,14]) {v : BitVec 64}
        (h : c[k] = ⟨64,v⟩) : mid.values[k] = c[k] := by
      apply (hkeep k hs).trans
      rw [h]
      rfl
    have final : mid.values[i] = c[i] := by
      have orig : c[i] = a[i] := (ckeep i hi).trans (bkeep i hk)
      obtain ⟨k,hk'⟩ := i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h|h|h|h|h|h|h <;> subst k
      · apply restored _ (by change 5 ∈ _; decide) (orig.trans bp)
      · apply restored _ (by change 13 ∈ _; decide) (orig.trans r13)
      · apply restored _ (by change 14 ∈ _; decide) (orig.trans r14)
      · exact hflags _ (by change 22 ∈ _; decide)
      · exact hflags _ (by change 39 ∈ _; decide)
      · exact hflags _ (by change 50 ∈ _; decide)
      · exact hflags _ (by change 51 ∈ _; decide)
    exact final.trans ((ckeep i hi).trans (bkeep i hk))
  have eq (d : Nat) (lo : d ≤ 136) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 d) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 :=
    finalFrame.memLoad_eq (outside lo (by decide))
  have rr' := rr.of_frame finalFrame
  have retEq : memLoad out.store fr.rsp 64 = memLoad m fr.rsp 64 := by
    simpa only [BitVec.sub_zero] using eq 0 (by decide)
  have ret' := retEq.trans ret
  have post : Atom.All Extracted.programImage out.values out.store (Fn104c90.frameAt .l104d5e fr) := by
    simp only [Fn104c90.frameAt,Fn104c90.frameAtG5,Atom.All,Atom.Holds]
    exact ⟨spBase ▸ outSp,(keep (by decide) (by decide)).trans df,outBx,
      (keep (by decide) (by decide)).trans bp,(keep (by decide) (by decide)).trans r13,
      (keep (by decide) (by decide)).trans r14,(keep (by decide) (by decide)).trans mx,
      (keep (by decide) (by decide)).trans ft,(keep (by decide) (by decide)).trans fc,
      (eq 32 (by decide)).trans s3,(eq 24 (by decide)).trans s12,
      (eq 16 (by decide)).trans s14,(eq 8 (by decide)).trans s15,
      rr',ret',small,stack.of_frame finalFrame,stackRoom,alignment,trivial⟩
  refine ⟨out.values,out.store,finish,⟨post,saved.frame.trans finalFrame inset⟩,?_,
    negated.of_frame finalFrame (by decide) (outside (d := 128) (by decide) (by decide))⟩
  rw [outFlag,compareBit_scalar input.sBound]
  split <;> rfl

end K256.Proofs.Signing.Scalar.Normalize
