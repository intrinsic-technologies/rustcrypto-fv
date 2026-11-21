import K256.Proofs.Verify.Core.Signature.Components
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.Core.Affine.Fill
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.Generator.Multiply.Prepare.HighBit

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply

private abbrev highKept : List Nat := [3,5,9,12,13,14,15,22,39,50,51]

local macro "high_kept" : tactic => `(tactic|
  (intro ⟨i,_⟩ hi
   simp only [highKept,List.mem_cons,List.not_mem_nil,or_false] at hi
   rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl))

private theorem highCarryLoad {m : Ram} {b a : BitVec 64} {n k : Nat} {v : BitVec k}
    (h : LoadOk m a n) : LoadOk (memStore m b v) a n :=
  ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi)⟩

private theorem highCarryStore {m : Ram} {b a p : BitVec 64} {n k len : Nat} {v : BitVec k}
    (h : StoreOk Extracted.programImage m a n p len) :
    StoreOk Extracted.programImage (memStore m b v) a n p len :=
  ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi), h.tables, h.apart, h.notCode⟩

private theorem highRead {m : Ram} {src : BitVec 64} (r : Readable m src 32)
    (off : BitVec 64) (fit : off.toNat + 8 ≤ 32) : LoadOk m (src+off) 8 := by
  apply LoadOk.of_offsets r (x := src) (c := off) (d := 0) rfl (addr_self src)
  rw [show off - (0 : BitVec 64) = off by bv_omega]
  exact fit

private def highStage (m : Ram) (sp : BitVec 64) (w : Vector (BitVec 64) 4) : Ram :=
  let m := memStore m (sp + 224) w[0]
  let m := memStore m (sp + 232) w[1]
  let m := memStore m (sp + 240) w[2]
  memStore m (sp + 248) w[3]

private theorem highStagedWords (m : Ram) (sp : BitVec 64) (w : Vector (BitVec 64) 4) :
    WordsAt (highStage m sp w) (sp + 224) 64 w := by
  intro i hi
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals simp (disch := store_disch) only [highStage, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
private theorem highSetup {a : Registers} {m : Ram} {sp src : BitVec 64} {w : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = sp) (ptr : a[15].get 64 + 32 = src)
    (read : Readable m src 32) (words : WordsAt m src 64 w)
    (write : Writable Extracted.programImage m (sp - 8) 264)
    (apart : ∀ i ∈ ([224,232,240] : List (BitVec 64)), ∀ j ∈ ([16,24] : List (BitVec 64)),
      RangeApart (sp+i) 8 (src+j) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l105069,a,m⟩ =
        .call ⟨.l10a170,b,memStore (highStage m sp w) (sp-8) (0x1050a9 : BitVec 64)⟩
          (Verify.resumeAt .l1050a9 0x1050a9) ∧
      b[4] = ⟨64,sp-8⟩ ∧ b[7] = ⟨64,sp+224⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ highKept → b[i] = a[i] := by
  have word (i : Nat) (hi : i < 4) :
      memLoad m (src + BitVec.ofNat 64 (8*i)) 64 = w[i] := words i hi
  have load0 : memLoad m src 64 = w[0] := by simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat,BitVec.add_zero] using word 0 (by decide)
  have load1 : memLoad m (src+8) 64 = w[1] := word 1 (by decide)
  have load2 : memLoad m (src+16) 64 = w[2] := word 2 (by decide)
  have load3 : memLoad m (src+24) 64 = w[3] := word 3 (by decide)
  have rd0 : LoadOk m src 8 := ⟨by have := read.low; omega, fun i hi => read.present i (by omega)⟩
  have rd1 := highRead read 8 (by decide)
  have rd2 := highRead read 16 (by decide)
  have rd3 := highRead read 24 (by decide)
  have wr (o : BitVec 64) (fit : (o - (0-8)).toNat + 8 ≤ 264) :
      Writable Extracted.programImage m (sp+o) 8 :=
    write.of_offsets rfl (addr_sub sp 8) fit
  have guard {addr : BitVec 64} (writable : Writable Extracted.programImage m addr 8)
      (off len : Nat) (fit : off+len ≤ bytes_l105069.length) :
      StoreOk Extracted.programImage m addr 8 (0x105069 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange writable
      (fun x hx => Common.fnCode_subset_programImage x (code_l105069 x hx)) fit
  have wr0 : StoreOk Extracted.programImage m (sp+224) 8 0x105074 8 := guard (wr 224 (by decide)) 11 8 (by decide)
  have wr1 : StoreOk Extracted.programImage m (sp+232) 8 0x10507c 8 := guard (wr 232 (by decide)) 19 8 (by decide)
  have wr2 : StoreOk Extracted.programImage m (sp+240) 8 0x105088 8 := guard (wr 240 (by decide)) 31 8 (by decide)
  have wr3 : StoreOk Extracted.programImage m (sp+248) 8 0x105094 8 := guard (wr 248 (by decide)) 43 8 (by decide)
  have wr4 : StoreOk Extracted.programImage m (sp-8) 8 0x1050a4 5 :=
    guard (write.sub (Nat.le_refl _) (by omega)) 59 5 (by decide)
  have unchanged (i j : BitVec 64) (hi : i ∈ ([224,232,240] : List (BitVec 64)))
      (hj : j ∈ ([16,24] : List (BitVec 64))) (m' : Ram) (v : BitVec 64) :
      memLoad (memStore m' (sp+i) v) (src+j) 64 = memLoad m' (src+j) 64 :=
    memLoad_memStore_of_rangeApart m' _ _ v 64 (apart i hi j hj)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,ptr,load0,load1,load2,load3,rd0,rd1,rd2,rd3,wr0,wr1,wr2,wr3,wr4]
    refine Eq.trans (ite_eq_left (highCarryStore wr1)) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad rd2))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore wr2))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad (highCarryLoad rd3)))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore (highCarryStore wr3)))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore (highCarryStore (highCarryStore wr4))))) ?_
    simp -failIfUnchanged (disch := decide) only [unchanged,load2,load3]
    rfl
  case post => exact ⟨rfl,rfl,by high_kept⟩

private theorem highLoad64 (m : Ram) (addr v : BitVec 64) :
    memLoad (memStore m addr v) addr 64 = v :=
  memLoad_memStore_same m addr v (by decide) (by decide)

private theorem highLoad8 (m : Ram) (addr v : BitVec 64) :
    memLoad (memStore m addr v) addr 8 = v.extractLsb' 0 8 :=
  Refine.memLoad_memStore_within m v 8 0 (BitVec.add_zero _).symm (by decide) (by decide) (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem highChoice {a : Registers} {m : Ram} {sp src : BitVec 64} {w : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = sp+8) (ptr : a[7].get 64 = src)
    (read : Readable m src 32) (words : WordsAt m src 64 w)
    (write : Writable Extracted.programImage m (sp-9) 17)
    (apart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), RangeApart sp 8 (src+i) 8)
    (spRoom : 9 ≤ sp.toNat) :
    ∃ b pre, program.runBlock (dialect Extracted.programImage) ⟨.l10a170,a,m⟩ =
        .call ⟨.l127d50,b,memStore pre (sp-8) (0x10a211 : BitVec 64)⟩
          (Verify.resumeAt .l10a211 0x10a211) ∧
      b[4] = ⟨64,sp-8⟩ ∧ b[7] = ⟨64,Prepare.highBit w[0] w[1] w[2] w[3]⟩ ∧
      RamWriteFrame m pre [⟨(sp-9).toNat,17⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ highKept → b[i] = a[i]) := by
  have word (i : Nat) (hi : i < 4) :
      memLoad m (src + BitVec.ofNat 64 (8*i)) 64 = w[i] := words i hi
  have load0 : memLoad m src 64 = w[0] := by simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat,BitVec.add_zero] using word 0 (by decide)
  have load1 : memLoad m (src+8) 64 = w[1] := word 1 (by decide)
  have load2 : memLoad m (src+16) 64 = w[2] := word 2 (by decide)
  have load3 : memLoad m (src+24) 64 = w[3] := word 3 (by decide)
  have apart0 : RangeApart sp 8 src 8 := (BitVec.add_zero src) ▸ apart 0 (by decide)
  have away {c : BitVec 64} (h : RangeApart sp 8 c 8) (m' : Ram) (v : BitVec 64) :
      memLoad (memStore m' sp v) c 64 = memLoad m' c 64 :=
    memLoad_memStore_of_rangeApart m' sp c v 64 h
  have away0 := away apart0
  have away1 := away (apart 8 (by decide))
  have away2 := away (apart 16 (by decide))
  have away3 := away (apart 24 (by decide))
  have scratch : Writable Extracted.programImage m sp 8 :=
    write.of_offsets (addr_self sp) (addr_sub sp 9) (by decide)
  have childSlot : Writable Extracted.programImage m (sp-8) 8 :=
    write.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  have base : (sp-9).toNat = sp.toNat-9 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr spRoom)
  have atSp : InRegions [⟨(sp-9).toNat,17⟩] sp 8 := by
    refine ⟨_,List.mem_singleton_self _,?_⟩
    have upper := write.readable.low
    simp only [InRegion,base] at *
    omega
  have rd0 : LoadOk m src 8 := ⟨by have := read.low; omega, fun i hi => read.present i (by omega)⟩
  have rd1 := highRead read 8 (by decide)
  have rd2 := highRead read 16 (by decide)
  have rd3 := highRead read 24 (by decide)
  have rdWord : LoadOk m sp 8 := ⟨scratch.readable.low,scratch.readable.present⟩
  have rdByte : LoadOk m sp 1 := LoadOk.of_region scratch.readable (Nat.le_refl _) (by omega)
  have guard {addr : BitVec 64} (writable : Writable Extracted.programImage m addr 8)
      (off len : Nat) (fit : off+len ≤ bytes_l10a170.length) :
      StoreOk Extracted.programImage m addr 8 (0x10a170 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange writable
      (fun x hx => Common.fnCode_subset_programImage x (code_l10a170 x hx)) fit
  have wr0 : StoreOk Extracted.programImage m sp 8 0x10a170 1 := guard scratch 0 1 (by decide)
  have wr1 : StoreOk Extracted.programImage m sp 8 0x10a188 4 := guard scratch 24 4 (by decide)
  have wr2 : StoreOk Extracted.programImage m sp 8 0x10a1b4 4 := guard scratch 68 4 (by decide)
  have wr3 : StoreOk Extracted.programImage m sp 8 0x10a1d8 4 := guard scratch 104 4 (by decide)
  have wr4 : StoreOk Extracted.programImage m sp 8 0x10a1ff 4 := guard scratch 143 4 (by decide)
  have wr5 : StoreOk Extracted.programImage m (sp-8) 8 0x10a20c 5 := guard childSlot 156 5 (by decide)
  refine ⟨?out, ?pre, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,ptr,load0,load1,load2,load3,BitVec.add_sub_cancel,away0,away1,away2,away3,
      highLoad64,highLoad8,rd0,rd1,rd2,rd3,rdWord,rdByte,wr0,wr1,wr2,wr3,wr4,wr5]
    refine Eq.trans (ite_eq_left (highCarryLoad rd0)) ?_
    refine Eq.trans (ite_eq_left (highCarryStore wr1)) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad rdWord))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad rd1))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore wr2))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad (highCarryLoad rdWord)))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad (highCarryLoad rd2)))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore (highCarryStore wr3)))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad (highCarryLoad (highCarryLoad rdWord))))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad (highCarryLoad (highCarryLoad rd3))))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore (highCarryStore (highCarryStore wr4))))) ?_
    refine Eq.trans (ite_eq_left (highCarryLoad (highCarryLoad (highCarryLoad (highCarryLoad (highCarryLoad rdByte)))))) ?_
    refine Eq.trans (ite_eq_left (highCarryStore (highCarryStore (highCarryStore (highCarryStore (highCarryStore wr5)))))) ?_
    simp only [away2,away3,load2,load3]
    rfl
  case post =>
    refine ⟨rfl,?_,?_,by high_kept⟩
    · simp only [BitVec.add_comm (0x7fffffffffffffff : BitVec 64) _, BitVec.add_comm (0x5d576e7357a4501d : BitVec 64) _]
      have hb := Prepare.highBit_correct w[0] w[1] w[2] w[3]
      change (⟨64, (mergeGPR 8 ((Prepare.highBit w[0] w[1] w[2] w[3]).extractLsb' 0 8 &&& 1)
        (((Prepare.highBit w[0] w[1] w[2] w[3]).extractLsb' 0 8).setWidth 64)).setWidth 8
          |>.setWidth 64⟩ : Value) = ⟨64, Prepare.highBit w[0] w[1] w[2] w[3]⟩
      rw [hb]
      split <;> rfl
    · iterate 5 apply RamWriteFrame.memStore _ _ atSp
      exact .refl _ _

private theorem highReturn {a : Registers} {m : Ram} {sp ret : BitVec 64}
    (rsp : a[4].get 64 = sp)
    (pop : LoadOk m sp 8) (read : LoadOk m (sp+8) 8)
    (addr : memLoad m (sp+8) 64 = ret) (small : ret.toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a211,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+16⟩ ∧
      out.values[0] = a[0] ∧ out.store = m ∧ (∀ i : Fin Reg.count, i.val ∈ highKept → out.values[i] = a[i]) := by
  refine ⟨?_, .done ?step, ?post⟩
  case step =>
    change program.step _ _ = _
    cfg_eval [rsp,pop,read,addr,small]
    rfl
  case post => exact ⟨rfl, rfl, rfl, rfl, by high_kept⟩

local macro "high_bounds" : tactic => `(tactic|
  (simp only [localSp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

private theorem highRun {a : Registers} {m : Ram} {sp src ret : BitVec 64} {w : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = sp+8) (ptr : a[7].get 64 = src)
    (read : Readable m src 32) (words : WordsAt m src 64 w)
    (write : Writable Extracted.programImage m (sp-9) 17)
    (apart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), RangeApart sp 8 (src+i) 8)
    (retRead : Readable m (sp+8) 8) (retAt : memLoad m (sp+8) 64 = ret) (small : ret.toNat < 2^32)
    (spRoom : 9 ≤ sp.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a170,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+16⟩ ∧
      out.values[0] = ⟨64, ((Prepare.highBit w[0] w[1] w[2] w[3]).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame m out.store [⟨(sp-9).toNat,17⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ highKept → out.values[i] = a[i]) := by
  obtain ⟨b,pre,call,bsp,bit,wrote,keep⟩ := highChoice rsp ptr read words write apart spRoom
  have hp := write.of_frame wrote
  have tmp : Writable Extracted.programImage pre (sp-8-1) 1 := by
    rw [show sp-8-1 = sp-9 by bv_omega]
    exact hp.sub (Nat.le_refl _) (by omega)
  have slot : Readable pre (sp-8) 8 :=
    hp.readable.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  obtain ⟨c,n,resumed,csp,byte,cframe,ckeep⟩ :=
    Verify.resumeChoice call (congrArg (Value.get 64) bsp) tmp slot (by decide)
  have writeLow := write.readable.low
  have base : (sp-9).toNat = sp.toNat-9 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr spRoom)
  have next : (sp-8).toNat = sp.toNat-8 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show 8 ≤ sp.toNat by omega))
  have top : (sp+8).toNat = sp.toNat+8 := by
    rw [base] at writeLow
    rw [BitVec.toNat_add]
    change (sp.toNat + 8) % 2^64 = sp.toNat + 8
    exact Nat.mod_eq_of_lt (by omega)
  let scratch : List MemoryRegion := [⟨(sp-9).toNat,17⟩]
  have full : RamWriteFrame m n scratch := by
    refine (wrote.memStore (0x10a211 : BitVec 64) ⟨_,List.mem_singleton_self _,?_⟩).trans cframe ?_
    · change (sp-9).toNat ≤ (sp-8).toNat ∧ (sp-8).toNat+8 ≤ (sp-9).toNat+17 ∧ _
      rw [base,next]
      rw [base] at writeLow
      omega
    · intro reg hreg
      obtain rfl := List.mem_singleton.mp hreg
      rw [show sp-8-1 = sp-9 by bv_omega]
      exact ⟨_,List.mem_singleton_self _,Nat.le_refl _, by dsimp only [scratch]; omega⟩
  have returnAddr : memLoad n (sp+8) 64 = ret := by
    refine (full.memLoad_eq ?_).trans retAt
    refine ⟨by omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp-9).toNat + 17 ≤ (sp+8).toNat
    omega
  have pop := (write.readable.of_frame full).of_offsets (len := 17) (n := 8)
    (addr_self sp) (addr_sub sp 9) (by decide)
  have retSlot := retRead.of_frame full
  obtain ⟨out,run,tag,stack,o0,store,okeep⟩ :=
    highReturn (congrArg (Value.get 64) csp) ⟨pop.low,pop.present⟩ ⟨retSlot.low,retSlot.present⟩ returnAddr small
  rw [bit] at byte
  refine ⟨out,Program.Exec.of_sem (resumed.exec run.sem),tag,stack,o0.trans byte,store.symm ▸ full,?_⟩
  intro i hi
  refine (okeep i hi).trans ((ckeep i ?_).trans (keep i hi))
  simp only [highKept,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  omega

private def highWrites (fr : Activation) : List MemoryRegion :=
  [⟨(localSp fr-25).toNat,25⟩,⟨(localSp fr+224).toNat,32⟩]

set_option maxHeartbeats 600000 in
theorem checkHigh {fr : Activation} {entry a : Registers} {m : Ram} {p : Curve.Point}
    {d : ByteArray} {r s : Nat} (e : Entry fr entry p d r s) (h : NonzeroComponents fr a m r) :
    ∃ b t, Reaches .l105069 a m .l1050a9 b t ∧ Parsed fr b t r s ∧
      (b[0].get 8 = 0 ↔ s ≤ domain.n / 2) := by
  let sp := localSp fr
  let src := fr.r8+32
  let w := scalarWords s
  have room := e.stackRoom
  have limit := e.low
  have bottom := e.low_toNat
  have sigAddr : src = fr.rsp+392 := by dsimp only [src]; rw [e.sig, BitVec.add_assoc]; rfl
  have read : Readable m src 32 :=
    ((e.upper.of_frame h.frame).of_offsets sigAddr rfl (by decide)).readable
  have win : Writable Extracted.programImage m (sp-8) 264 := by
    rw [show sp-8 = fr.rsp - 496 by dsimp only [sp,localSp]; bv_omega]
    exact Affine.coreWindow e h.frame (d := 496) (by decide) (by decide)
  have atoms := h.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,_,_,_,r12,r13,r14,r15,_,_,_,_,_,_,_,_,retRead,retAt,retLow,stack,roomOld,
    align,rd0,got0,rd1,got1,rd2,got2,gotApart,_⟩ := atoms
  have setupApart (i : BitVec 64) (hi : i ∈ ([224,232,240] : List (BitVec 64)))
      (j : BitVec 64) (hj : j ∈ ([16,24] : List (BitVec 64))) : RangeApart (sp+i) 8 (src+j) 8 := by
    have left (i : BitVec 64) : sp+i = fr.rsp + ((0-488)+i) := by
      dsimp only [sp,localSp]
      bv_omega
    have right (j : BitVec 64) : src+j = fr.rsp + (392+j) := by
      rw [sigAddr,BitVec.add_assoc]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi hj
    rcases hi with h₁ | h₁ | h₁ <;> rcases hj with h₂ | h₂ <;> subst i <;> subst j <;>
      exact RangeApart.of_offsets (left _) (right _) (by decide)
  obtain ⟨args,call,argsSp,argsPtr,keep⟩ := highSetup (congrArg (Value.get 64) h.sp)
    (congrArg (fun v : Value => v.get 64 + 32) r15) read (e.scalarWords_of_frame h.frame).2 win setupApart
  let staged := highStage m sp w
  let pushed := memStore staged (sp-8) (0x1050a9 : BitVec 64)
  have stagedFrame : RamWriteFrame m staged (highWrites fr) := by
    have slot (i : BitVec 64) (hi : i ∈ ([224,232,240,248] : List (BitVec 64))) :
        InRegions (highWrites fr) (sp+i) 8 := by
      refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> dsimp only [InRegion,sp] <;> high_bounds
    dsimp only [staged,highStage]
    repeat' apply RamWriteFrame.memStore _ _ (slot _ (by decide))
    exact .refl _ _
  let callWrites : List MemoryRegion := [⟨(sp-25).toNat,25⟩]
  have includes : RegionsWithin callWrites (highWrites fr) := by
    intro rg hm
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  have pushedFrame : RamWriteFrame staged pushed callWrites := by
    apply (RamWriteFrame.refl staged callWrites).memStore
    refine ⟨_,List.mem_singleton_self _,?_⟩
    dsimp only [InRegion,sp]
    high_bounds
  have area := (e.stack.of_frame h.frame).of_frame (stagedFrame.trans pushedFrame includes)
  have input : Readable pushed (sp+224) 32 := by
    apply area.readable.sub <;> dsimp only [sp] <;> high_bounds
  have scratch : Writable Extracted.programImage pushed (sp-16-9) 17 := by
    apply area.sub <;> dsimp only [sp] <;> high_bounds
  have rootRet : Readable pushed (sp-8) 8 := by
    apply area.readable.sub <;> dsimp only [sp] <;> high_bounds
  have callApart (i : BitVec 64) (hi : i ∈ ([0,8,16,24] : List (BitVec 64))) :
      RangeApart (sp-16) 8 (sp+224+i) 8 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact RangeApart.of_offsets (addr_sub sp 16) (BitVec.add_assoc _ _ _) (by decide)
  have stagedWords : WordsAt pushed (sp+224) 64 w :=
    (highStagedWords m sp w).write_apart _ _
      (RangeApart.of_offsets (addr_sub sp 8) rfl (by decide))
  have childPlus8 : sp-16+8 = sp-8 := by bv_omega
  have childPlus16 : sp-16+16 = sp := BitVec.sub_add_cancel _ _
  obtain ⟨out,run,tag,outSp,outByte,outFrame,outKeep⟩ :=
    highRun (sp := sp-16) (by rw [childPlus8]; exact congrArg (Value.get 64) argsSp)
      (congrArg (Value.get 64) argsPtr) input stagedWords scratch callApart
      (childPlus8.symm ▸ rootRet) (childPlus8.symm ▸ memLoad_memStore_same staged (sp-8) _ (by decide) (by decide))
      (by decide : (0x1050a9 : BitVec 64).toNat < 2^32) (by dsimp only [sp]; high_bounds)
  rw [childPlus16] at outSp
  have finish := Verify.reachesOfCall call run tag
  have callFrame := pushedFrame.trans outFrame (by
    intro reg hreg
    obtain rfl := List.mem_singleton.mp hreg
    refine ⟨_,List.mem_singleton_self _,?_⟩
    rw [show sp-16-9 = sp-25 by bv_omega]
    exact ⟨Nat.le_refl _,Nat.add_le_add_left (by decide : 17 ≤ 25) _⟩)
  have delta := stagedFrame.trans callFrame includes
  have within : ∀ rg ∈ highWrites fr, fr.low.toNat ≤ rg.start ∧
      rg.start + rg.size ≤ fr.rsp.toNat - 40 := by
    intro rg hm
    simp only [highWrites,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> dsimp only <;> high_bounds
  have kept (i : Fin Reg.count) (hi : i.val ∈ highKept) : out.values[i] = a[i] :=
    (outKeep i hi).trans (keep i hi)
  have phase := Affine.phaseFrame e h.toPhase outSp ((kept 3 (by decide)).trans h.dst)
    ((kept 5 (by decide)).trans h.rbp) ((kept 22 (by decide)).trans h.df)
    ((kept 39 (by decide)).trans h.mxcsr) ((kept 50 (by decide)).trans h.ftw)
    ((kept 51 (by decide)).trans h.fcw) delta within
  have preserved (base : BitVec 64) (len : Nat) (low : (localSp fr+256).toNat ≤ base.toNat)
      (hi : base.toNat+len ≤ 2^64) : Outside (highWrites fr) base len := by
    refine ⟨hi,fun reg hm => ?_⟩
    simp only [highWrites,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> right <;> dsimp only <;> high_bounds
  have rAt := h.rAt.of_frame delta (by decide) (preserved _ _ (Nat.le_refl _) (by high_bounds))
  have sAt := (highStagedWords m sp w).of_frame callFrame (by decide) (by
    refine ⟨by dsimp only [sp]; high_bounds, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [sp]
    high_bounds)
  have loadRet : memLoad out.store fr.rsp 64 = fr.ret :=
    (delta.memLoad_eq (preserved _ _ (by high_bounds) (by high_bounds))).trans retAt
  have got {v : BitVec 64} (low : 0x203dd0 ≤ v.toNat)
      (high : v.toNat+8 ≤ 0x203e28) : Outside (highWrites fr) v 8 := by
    refine ⟨by omega, fun reg hm => ?_⟩
    have loc : 0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 := gotApart
    have w := within reg hm
    simp only [highWrites,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> dsimp only at w ⊢ <;> high_bounds
  have parsedAtoms : Atom.All Extracted.programImage out.values out.store (Fn104f20.frameAt .l1050c1 fr) :=
    ⟨outSp,phase.df,phase.dst,phase.rbp,(kept 12 (by decide)).trans r12,(kept 13 (by decide)).trans r13,
      (kept 14 (by decide)).trans r14,(kept 15 (by decide)).trans r15,phase.mxcsr,phase.ftw,phase.fcw,
      phase.rbx,phase.r12,phase.r13,phase.r14,phase.r15,retRead.of_frame delta,loadRet,retLow,
      stack.of_frame delta,roomOld,align,rd0.of_frame delta,(delta.memLoad_eq (got (by decide) (by decide))).trans got0,
      rd1.of_frame delta,(delta.memLoad_eq (got (by decide) (by decide))).trans got1,
      rd2.of_frame delta,(delta.memLoad_eq (got (by decide) (by decide))).trans got2,gotApart,trivial⟩
  refine ⟨out.values,out.store,finish,⟨phase,(congrArg Value.width (kept 9 (by decide))).trans h.r9Width,
    parsedAtoms,rAt,sAt⟩,?_⟩
  have bit := Prepare.highBit_correct w[0] w[1] w[2] w[3]
  change Prepare.highBit w[0] w[1] w[2] w[3] = (if domain.n / 2 < Split.scalarValue w then 1 else 0) at bit
  have bound : s < 2^256 := Nat.lt_trans e.bounds.2.2.2 (by decide +kernel)
  change Prepare.highBit w[0] w[1] w[2] w[3] = (if domain.n / 2 < Split.scalarValue (scalarWords s) then 1 else 0) at bit
  rw [Split.scalarWords_value s bound] at bit
  rw [outByte,bit]
  by_cases hi : domain.n / 2 < s
  · simp only [hi,ite_true]
    exact iff_of_false (by decide) (by omega)
  · simp only [hi,ite_false]
    exact iff_of_true (by decide) (by omega)


end K256.Proofs.Verify.Core
