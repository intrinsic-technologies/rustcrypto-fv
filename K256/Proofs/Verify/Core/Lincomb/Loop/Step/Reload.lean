import K256.Proofs.Verify.Core.Lincomb.Loop.Column
import K256.Proofs.Verify.Core.Lincomb.Loop.Packed

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)

private theorem reloadJump {l r : Label} {a b : Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨r,b,n⟩) :
    Reaches l a m r b n := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  rw [run]
  rfl

private theorem reloadBlocks {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base)
    (wr : StoreOk Extracted.programImage m (base + 40) 8 0x110307 5)
    (word : BitVec 64) (hw : word = mergeGPR 8 1 (a[0].get 64))
    (load : ∀ off : BitVec 64, off.toNat ≤ 32 →
      LoadOk (memStore m (base + 40) word) (base + off) 8) :
    let n := memStore m (base+40) word
    ∃ b, Reaches .l110305 a m .l11037b b n ∧
      b[8] = ⟨64,memLoad n base 64⟩ ∧ b[9] = ⟨64,memLoad n (base+16) 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  intro n
  have l0 := load 0 (by decide)
  rw [show base + (0 : BitVec 64) = base by bv_omega] at l0
  have l8 := load 8 (by decide)
  have l16 := load 16 (by decide)
  have l32 := load 32 (by decide)
  obtain ⟨b,run,reg,back,count,keep⟩ : ∃ b, Reaches .l110305 a m .l11031a b n ∧
      b[4].get 64 = base ∧ b[8] = ⟨64,memLoad n base 64⟩ ∧
      b[9] = ⟨64,memLoad n (base+16) 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
    refine ⟨?_,reloadJump ?edge,?post⟩
    case edge =>
      cfg_eval [rsp,wr,← hw,l0,l8,l16]
      rfl
    case post =>
      refine ⟨rsp,rfl,rfl,?_⟩
      rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine ⟨?_,run.trans (reloadJump ?edge),?post⟩
  case edge =>
    cfg_eval [reg,l32]
    rfl
  case post =>
    refine ⟨back,count,?_⟩
    rintro ⟨i,hi⟩ h
    have := keep ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact this

theorem reloadDigit {a b c : Registers} {m n store : Ram} {sp dst table : BitVec 64}
    {k : Nat} {value : Curve.Point} {res : Projective} {j : Fin 4}
    (entry : RoutineEntry a m sp 0x478) (state : Column a m sp dst table k value b n)
    (cursor : Cursor sp table j (j.val%2+1) b n) (rsp : c[4] = ⟨64,baseSp sp⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → c[i] = b[i])
    (point : res.Stored store (baseSp sp + 0x130)) (valid : res.valid)
    (frame : RamWriteFrame n store (digitWrites (baseSp sp) ++
      [scratch (baseSp sp) 544, ⟨(baseSp sp+0x130).toNat,120⟩])) :
    ∃ d t, Reaches .l110305 c store .l11037b d t ∧
      Column a m sp dst table k res.value d t ∧ Cursor sp table j (j.val%2+1) d t := by
  let base := baseSp sp
  let word := mergeGPR 8 1 (c[0].get 64)
  let t := memStore store (base+40) word
  have room := entry.room
  have low := entry.returnSlot.low
  have sub (off : BitVec 64) (h : off.toNat ≤ 0x478) : (sp-off).toNat = sp.toNat-off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have baseNat : base.toNat = sp.toNat - 0x1d8 := sub _ (by decide)
  have add (off : BitVec 64) (h : off.toNat ≤ 0x1d8) :
      (base+off).toNat = base.toNat + off.toNat := by
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have flagNat : (base+40).toNat = base.toNat+40 := add 40 (by decide)
  have firstNat : (base+88).toNat = base.toNat+88 := add 88 (by decide)
  have secondNat : (base+224).toNat = base.toNat+224 := add 224 (by decide)
  have pointNat : (base+304).toNat = base.toNat+304 := add 304 (by decide)
  let flag : MemoryRegion := ⟨(base+40).toNat,8⟩
  let areas := flag :: (digitWrites base ++ [scratch base 544, ⟨(base+304).toNat,120⟩])
  have flagFrame : RamWriteFrame store t [flag] :=
    (RamWriteFrame.refl _ _).memStore word ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by omega⟩
  have changed : RamWriteFrame n t areas := by
    apply ((RamWriteFrame.refl n areas).trans frame ?_).memStore word
    · exact ⟨flag,.head _,Nat.le_refl _,Nat.le_refl _,by omega⟩
    · intro r hr
      exact ⟨r,.tail _ hr,Nat.le_refl _,Nat.le_refl _⟩
  have stackFrame : RamWriteFrame m t [scratch sp 0x478] := by
    apply state.frame.trans changed
    intro r hr
    refine ⟨_,.head _,?_⟩
    change sp.toNat-0x478 ≤ r.start ∧ r.start+r.size ≤ sp.toNat-0x478+0x478
    simp only [areas, digitWrites, List.cons_append,List.nil_append,List.mem_cons,
      List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> dsimp only [flag,scratch] <;> omega
  have same (ptr : BitVec 64) (lo : base.toNat ≤ ptr.toNat) (hi : ptr.toNat+8 ≤ sp.toNat)
      (flagSep : ptr.toNat+8 ≤ base.toNat+40 ∨ base.toNat+48 ≤ ptr.toNat)
      (bufSep : ptr.toNat+8 ≤ base.toNat+88 ∨ base.toNat+208 ≤ ptr.toNat)
      (ySep : ptr.toNat+8 ≤ base.toNat+224 ∨ base.toNat+304 ≤ ptr.toNat)
      (qSep : ptr.toNat+8 ≤ base.toNat+304 ∨ base.toNat+424 ≤ ptr.toNat) :
      memLoad t ptr 64 = memLoad n ptr 64 := by
    apply changed.memLoad_eq
    refine ⟨by omega,fun r hr => ?_⟩
    simp only [areas, digitWrites,List.cons_append,List.nil_append,List.mem_cons,
      List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> dsimp only [flag,scratch] <;> omega
  have saved (off : BitVec 64) (h : off.toNat ≤ 48) (pos : 8 ≤ off.toNat) :
      memLoad t (sp-off) 64 = memLoad n (sp-off) 64 := by
    have addr := sub off (by omega)
    apply same <;> omega
  have slot (off : BitVec 64) (h : off.toNat ∈ [0,16,24,56,64,208]) :
      memLoad t (base+off) 64 = memLoad n (base+off) 64 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have := add off (by omega)
    apply same <;> omega
  have back := slot 0 (by decide)
  rw [show base + (0 : BitVec 64) = base by bv_omega] at back
  have wr : Writable Extracted.programImage store (base+40) 8 :=
    ((entry.stack.of_frame state.frame).of_frame frame).of_offsets
      (x := sp) (c := -(0x1d8-40)) (d := -0x478) (by dsimp [base,baseSp]; bv_omega)
      (by bv_omega) (by decide)
  have ok : StoreOk Extracted.programImage store (base+40) 8 0x110307 5 :=
    ParseSignature.storeOk_of_codeRange (off := 2) wr
      (fun x hx => Common.fnCode_subset_programImage x (code_l110305 x hx)) (by decide)
  have load (off : BitVec 64) (small : off.toNat ≤ 32) : LoadOk t (base+off) 8 := by
    have start : (sp-BitVec.ofNat 64 0x478).toNat = sp.toNat-0x478 := sub _ (by decide)
    have addr := add off (by omega)
    apply LoadOk.of_region (entry.stack.readable.of_frame stackFrame) <;> omega
  obtain ⟨d,run,r8,r9,regs⟩ := reloadBlocks (congrArg (Value.get 64) rsp) ok word rfl load
  have both (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :=
    (regs i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] →
      i.val ∈ [3,4,5,12,13,14,15,22,39,50,51]) i h)).trans (keep i h)
  have loadedBack := back.trans state.savedBack
  have loadedCounter := (slot 16 (by decide)).trans state.savedCounter
  refine ⟨d,t,run,⟨⟨(regs 4 (by decide)).trans rsp,(slot _ (by decide)).trans state.dest,
    (saved _ (by decide) (by decide)).trans state.rbx,(saved _ (by decide) (by decide)).trans state.r12,
    (saved _ (by decide) (by decide)).trans state.r13,(saved _ (by decide) (by decide)).trans state.r14,
    (saved _ (by decide) (by decide)).trans state.r15,(saved _ (by decide) (by decide)).trans state.rbp,
    ?_,stackFrame⟩,(both 5 (by decide)).trans state.last,r8.trans (congrArg (Value.mk 64) loadedBack),
    r9.trans (congrArg (Value.mk 64) loadedCounter),loadedCounter,(slot _ (by decide)).trans state.savedFront,
    (slot _ (by decide)).trans state.savedNext,loadedBack,⟨res,point.of_frame flagFrame ?_,valid,rfl⟩,?_⟩,
    (both 3 (by decide)).trans cursor.count,(both 12 (by decide)).trans cursor.component,
    (both 13 (by decide)).trans cursor.base,(both 14 (by decide)).trans cursor.next,
    (slot _ (by decide)).trans cursor.digits⟩
  · intro i h
    exact (both i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] →
      i.val ∈ [3,5,12,13,14,15,22,39,50,51]) i h)).trans (state.control i h)
  · change Outside [flag] (base+304) 120
    refine ⟨by omega,fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change _ ∨ (base+40).toNat+8 ≤ (base+304).toNat
    omega
  · change (memLoad (memStore store (base+40) word) (base+40) 8 &&& 1) = 0 → _
    rw [memLoad_memStore_within store word 8 0 (by simp) (by decide) (by decide) (by decide)]
    change (word.setWidth 8 &&& 1) = 0 → _
    rw [show word.setWidth 8 = 1 from setWidth_mergeGPR8 _ _]
    intro h
    exact False.elim ((by decide : (1 &&& 1 : BitVec 8) ≠ 0) h)

end K256.Proofs.Verify.Core.Lincomb.Loop
