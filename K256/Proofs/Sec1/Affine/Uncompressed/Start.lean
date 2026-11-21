import K256.Proofs.Sec1.Affine.Uncompressed.Contract
import K256.Proofs.Sec1.Affine.Uncompressed.Complement
import K256.Proofs.Sec1.Affine.Uncompressed.Choice

namespace K256.Proofs.Sec1.Affine.Uncompressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

private theorem singleWithin {a b : MemoryRegion}
    (lo : b.start ≤ a.start) (hi : a.start + a.size ≤ b.start + b.size) :
    RegionsWithin [a] [b] := by
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact ⟨b, List.mem_cons_self, lo, hi⟩

private theorem subNat {sp k : Word} {n : Nat} (hk : k.toNat = n) (h : n ≤ sp.toNat) :
    (sp - k).toNat = sp.toNat - n := by
  have le : k ≤ sp := BitVec.le_def.mpr (hk.symm ▸ h)
  rw [BitVec.toNat_sub_of_le le, hk]

private theorem loadStoreOffset (m : Ram) (sp a b : Word) (v : Word)
    (h : 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :
    memLoad (memStore m (sp + a) v) (sp + b) 64 = memLoad m (sp + b) 64 :=
  memLoad_memStore_of_rangeApart m _ _ v 64 (RangeApart.of_offsets rfl rfl h)

private theorem loadStoreSub (m : Ram) (sp a b : Word) (v : Word)
    (h : 8 ≤ ((0 - b) - (0 - a)).toNat ∧ 8 ≤ ((0 - a) - (0 - b)).toNat) :
    memLoad (memStore m (sp - a) v) (sp - b) 64 = memLoad m (sp - b) 64 :=
  memLoad_memStore_of_rangeApart m _ _ v 64
    (RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) h)

private theorem savedSlots (args : Values Value Reg.count) (m : Ram) (sp : Word) :
    SavedWords args (saved args m sp) sp ∧
      memLoad (saved args m sp) (sp - 56) 64 = args[7].get 64 := by
  simp (disch := decide) only [SavedWords, saved, loadStoreSub, memLoad_memStore_same, and_self]

private theorem invalidValid (c : CoordinateWords) : invalid c.a c.b c.c c.d = !c.valid := by
  rw [invalid_eq]
  change decide (modulus ≤ c.nat) = !decide (c.nat < modulus)
  simpa only [Nat.not_lt] using (decide_not (p := c.nat < modulus))

private theorem bit8 (b : Bool) :
    ((BitVec.ofNat 64 b.toNat).setWidth 8).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

private theorem lowBit (b : Bool) :
    (BitVec.ofNat 64 b.toNat).setWidth 8 = BitVec.ofNat 8 b.toNat := by
  cases b <;> rfl

private theorem loadInput {o m : Ram} {sp p : Word}
    (frame : RamWriteFrame o m [⟨(sp - 273).toNat, 273⟩])
    (room : 273 ≤ sp.toNat) (read : Readable o p 32)
    (apart : p.toNat + 32 ≤ sp.toNat - 273 ∨ sp.toNat ≤ p.toNat)
    (off : Word) (bound : off.toNat + 8 ≤ 32) :
    memLoad m (p + off) 64 = memLoad o (p + off) 64 := by
  have low := read.low
  have addr : (p + off).toNat = p.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  apply frame.memLoad_eq
  refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
  rcases List.mem_singleton.mp hr with rfl
  change (p + off).toNat + 8 ≤ (sp - 273).toNat ∨
    (sp - 273).toNat + 273 ≤ (p + off).toNat
  rw [addr, subNat (k := 273) (n := 273) rfl room]
  omega

private theorem storeWorking {o m : Ram} {w off : Word} (v : Word)
    (h : RamWriteFrame o m [⟨(w - 9).toNat, 217⟩])
    (room : 9 ≤ w.toNat) (low : w.toNat + 208 ≤ 2^64) (bound : off.toNat + 8 ≤ 208) :
    RamWriteFrame o (memStore m (w + off) v) [⟨(w - 9).toNat, 217⟩] := by
  have addr : (w + off).toNat = w.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  apply h.memStore
  refine ⟨_, List.mem_cons_self, ?_⟩
  change (w - 9).toNat ≤ (w + off).toNat ∧
    (w + off).toNat + 8 ≤ (w - 9).toNat + 217 ∧ (w + off).toNat + 8 ≤ 2^64
  rw [addr, subNat (k := 9) (n := 9) rfl room]
  omega

private theorem resumePushedChoice {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code)
    {caller : Location Value Ram Label signature} {target : Label} {ret w : Word}
    {args : Values Value Reg.count} {m : Ram} {bit : Bool}
    (step : program.runBlock (dialect code) caller =
      .call ⟨.l127d50,args,memStore m (w - 8) ret⟩ (choiceResume target ret rfl))
    (rsp : args[4].get 64 = w - 8) (stack : Writable code m (w - 9) 9)
    (room : 9 ≤ w.toNat) (low : ret.toNat < 2^32)
    (arg : args[7].get 64 = BitVec.ofNat 64 bit.toNat) :
    ∃ (regs : Values Value Reg.count) (after : Ram),
      (program.sem (dialect code)).Reaches ⟨caller,[]⟩ ⟨⟨target,regs,after⟩,[]⟩ ∧
      regs[4].get 64 = w ∧ regs[0].get 64 = BitVec.ofNat 64 bit.toNat ∧
      RamWriteFrame m after [⟨(w-9).toNat,9⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        regs[i] = args[i] := by
  have push : RamWriteFrame m (memStore m (w-8) ret) [⟨(w-9).toNat,9⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (w-9).toNat ≤ (w-8).toNat ∧ (w-8).toNat + 8 ≤ (w-9).toNat + 9 ∧
      (w-8).toNat + 8 ≤ 2^64
    rw [subNat (k := 9) (n := 9) rfl room, subNat (k := 8) (n := 8) rfl (by omega)]
    have := w.isLt
    omega
  obtain ⟨regs, after, reach, stack', byte, frame, kept⟩ := resumeChoice cover step rsp
    (stack.of_frame push) (memLoad_memStore_same _ _ _ (by decide) (by decide)) low
  refine ⟨regs, after, reach, ?_, ?_, push.trans frame (singleWithin (Nat.le_refl _) (Nat.add_le_add_left (by decide : 1 ≤ 9) _)), kept⟩
  · rw [stack']; rfl
  · rw [byte, arg]; exact bit8 bit

private theorem resumeComplement {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code)
    (y : Bool) (args : Values Value Reg.count) (m : Ram) (w : Word) (bit : Bool)
    (rsp : args[4].get 64 = w) (byte : args[0].get 64 = BitVec.ofNat 64 bit.toNat)
    (stack : Writable code m (w - 9) 9) (room : 9 ≤ w.toNat) :
    ∃ (regs : Values Value Reg.count) (after : Ram),
      (program.sem (dialect code)).Reaches
        ⟨⟨if y then .l11f8ea else .l11f825,args,m⟩,[]⟩
        ⟨⟨if y then .l11f8f6 else .l11f831,regs,after⟩,[]⟩ ∧
      regs[4].get 64 = w ∧ regs[0].get 64 = BitVec.ofNat 64 (!bit).toNat ∧
      RamWriteFrame m after [⟨(w-9).toNat,9⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [2,3,5,6,12,13,14,15,22,39,50,51] →
        regs[i] = args[i] := by
  have win : Writable code m (w - 8) 8 :=
    stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have push : StoreOk code m (w - 8) 8 (if y then 0x11f8f1 else 0x11f82c) 5 := by
    cases y
    · exact ParseSignature.storeOk_of_codeRange (off := 7) win
        (fun v hv => cover v (code_l11f825 v hv)) (by decide)
    · exact ParseSignature.storeOk_of_codeRange (off := 7) win
        (fun v hv => cover v (code_l11f8ea v hv)) (by decide)
  obtain ⟨next, run, nextSP, nextBit, keep⟩ :=
    complementChoice y code args m w rsp bit (byte ▸ lowBit bit) push
  have compose {regs : Values Value Reg.count}
      (keep' : ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        regs[i] = next[i]) (i : Fin Reg.count) (hi : i.val ∈ [2,3,5,6,12,13,14,15,22,39,50,51]) :
      regs[i] = args[i] := by
    rw [keep' i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    exact keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  cases y
  · obtain ⟨r, a, reach, sr, br, f, k⟩ := resumePushedChoice cover run nextSP stack room (by decide) nextBit
    exact ⟨r, a, reach, sr, br, f, compose k⟩
  · obtain ⟨r, a, reach, sr, br, f, k⟩ := resumePushedChoice cover run nextSP stack room (by decide) nextBit
    exact ⟨r, a, reach, sr, br, f, compose k⟩

private theorem resumeCanonical {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code)
    (y : Bool) {caller : Location Value Ram Label signature} {ret w : Word}
    {args : Values Value Reg.count} {m : Ram} {valid : Bool}
    (step : program.runBlock (dialect code) caller =
      .call ⟨.l127d50,args,memStore m (w - 8) ret⟩
        (choiceResume (if y then .l11f8ea else .l11f825) ret rfl))
    (rsp : args[4].get 64 = w - 8) (stack : Writable code m (w - 9) 9)
    (room : 9 ≤ w.toNat) (low : ret.toNat < 2^32)
    (arg : args[7].get 64 = BitVec.ofNat 64 (!valid).toNat) :
    ∃ (regs : Values Value Reg.count) (after : Ram),
      (program.sem (dialect code)).Reaches ⟨caller,[]⟩
        ⟨⟨if y then .l11f8f6 else .l11f831,regs,after⟩,[]⟩ ∧
      regs[4].get 64 = w ∧ regs[0].get 64 = BitVec.ofNat 64 valid.toNat ∧
      RamWriteFrame m after [⟨(w-9).toNat,9⟩] ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        regs[i] = args[i] := by
  obtain ⟨a, n, first, sp, byte, writes, kept⟩ :=
    resumePushedChoice cover step rsp stack room low arg
  obtain ⟨regs, after, next, sp', byte', writes', kept'⟩ :=
    resumeComplement cover y a n w (!valid) sp byte (stack.of_frame writes) room
  rw [Bool.not_not] at byte'
  refine ⟨regs, after, first.trans next, sp', byte',
    writes.trans writes' (singleWithin (Nat.le_refl _) (Nat.le_refl _)), ?_⟩
  intro i hi
  rw [kept' i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
  exact kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)

private def coordinatePrefix (m : Ram) (w : Word) (x : CoordinateWords) : Ram :=
  let bit := BitVec.ofNat 64 x.valid.toNat
  let m := memStore m (w + 200) bit
  let m := memStore m (w + 80) ((x.d &&& 0xfffffffffffff) &&& -bit)
  let m := memStore m (w + 48) ((shldResult 12 x.c x.d &&& 0xfffffffffffff) &&& -bit)
  memStore m (w + 32) ((x.a >>> 16) &&& -bit)

private def coordinateMiddle (m : Ram) (w : Word) (x : CoordinateWords) : Ram :=
  let mask := -(BitVec.ofNat 64 x.valid.toNat) &&& 0xfffffffffffff
  memStore (coordinatePrefix m w x) (w + 88) (shldResult 24 x.b x.c &&& mask)

private def coordinateStore (m : Ram) (w : Word) (x : CoordinateWords) : Ram :=
  let mask := -(BitVec.ofNat 64 x.valid.toNat) &&& 0xfffffffffffff
  memStore (coordinateMiddle m w x) (w + 56) (mask &&& shldResult 36 x.a x.b)

private theorem coordinatePrefixFrame (m : Ram) (w : Word) (x : CoordinateWords)
    (room : 9 ≤ w.toNat) (low : w.toNat + 208 ≤ 2^64) :
    RamWriteFrame m (coordinatePrefix m w x) [⟨(w - 9).toNat,217⟩] := by
  unfold coordinatePrefix
  repeat' refine storeWorking _ ?_ room low (by decide)
  apply RamWriteFrame.refl

private theorem coordinateMiddleFrame (m : Ram) (w : Word) (x : CoordinateWords)
    (room : 9 ≤ w.toNat) (low : w.toNat + 208 ≤ 2^64) :
    RamWriteFrame m (coordinateMiddle m w x) [⟨(w - 9).toNat,217⟩] :=
  storeWorking _ (coordinatePrefixFrame m w x room low) room low (by decide)

private theorem coordinateStoreFrame (m : Ram) (w : Word) (x : CoordinateWords)
    (room : 9 ≤ w.toNat) (low : w.toNat + 208 ≤ 2^64) :
    RamWriteFrame m (coordinateStore m w x) [⟨(w - 9).toNat,217⟩] :=
  storeWorking _ (coordinateMiddleFrame m w x room low) room low (by decide)

private theorem coordinateStoreFlag (m : Ram) (w : Word) (x : CoordinateWords) :
    memLoad (coordinateStore m w x) (w + 200) 64 = BitVec.ofNat 64 x.valid.toNat := by
  simp (disch := decide) only [coordinateStore, coordinateMiddle, coordinatePrefix,
    loadStoreOffset, memLoad_memStore_same]

private theorem maskedGet (x : CoordinateWords) (i : Nat) (hi : i < 5) :
    x.masked[i] = if x.valid then x.limbs[i] else 0 := by
  unfold CoordinateWords.masked
  split <;> simp only [Vector.getElem_replicate]

private theorem maskWord (b : Bool) (v : Word) :
    v &&& -(BitVec.ofNat 64 b.toNat) = if b then v else 0 := by
  cases b
  · change v &&& 0 = 0
    exact BitVec.and_zero
  · change v &&& BitVec.allOnes 64 = v
    exact BitVec.and_allOnes

private theorem coordinateStoreLimbs (m : Ram) (w : Word) (x : CoordinateWords) :
    localLimbs (coordinateStore m w x) w false = x.masked := by
  apply Vector.ext
  intro i hi
  have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases index with rfl | rfl | rfl | rfl | rfl
  · change memLoad (coordinateStore m w x) (w + 80) 64 = x.masked[0]
    simp (disch := decide) only [coordinateStore, coordinateMiddle, coordinatePrefix,
      loadStoreOffset, memLoad_memStore_same, maskedGet, maskWord]
    rfl
  · change memLoad (coordinateStore m w x) (w + 48) 64 = x.masked[1]
    simp (disch := decide) only [coordinateStore, coordinateMiddle, coordinatePrefix,
      loadStoreOffset, memLoad_memStore_same, maskedGet, maskWord]
    rfl
  · change memLoad (coordinateStore m w x) (w + 88) 64 = x.masked[2]
    simp (disch := decide) only [coordinateStore, coordinateMiddle, coordinatePrefix,
      loadStoreOffset, memLoad_memStore_same, maskedGet]
    rw [← maskWord]
    change _ = shldResult 24 x.b x.c &&& 0xfffffffffffff &&& -(BitVec.ofNat 64 x.valid.toNat)
    ac_rfl
  · change memLoad (coordinateStore m w x) (w + 56) 64 = x.masked[3]
    simp (disch := decide) only [coordinateStore, coordinateMiddle, coordinatePrefix,
      memLoad_memStore_same, maskedGet]
    rw [← maskWord]
    change _ = shldResult 36 x.a x.b &&& 0xfffffffffffff &&& -(BitVec.ofNat 64 x.valid.toNat)
    ac_rfl
  · change memLoad (coordinateStore m w x) (w + 32) 64 = x.masked[4]
    simp (disch := decide) only [coordinateStore, coordinateMiddle, coordinatePrefix,
      loadStoreOffset, memLoad_memStore_same, maskedGet, maskWord]
    rfl

private theorem coordinateReg {a b : Values Value Reg.count} {live : List Nat}
    (keep : ∀ i : Fin Reg.count, i.val ∈ live → a[i] = b[i])
    (i : Nat) (bound : i < Reg.count) (hi : i ∈ live) :
    a[i].get 64 = b[i].get 64 :=
  congrArg (Value.get 64) (keep ⟨i, bound⟩ hi)

set_option maxRecDepth 4096 in
theorem startCall {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) : StartCall code := by
  intro args mem sp dst x y ret pre
  let w := sp - 264
  let cx := readCoordinate mem x
  let cy := readCoordinate mem y
  let ms := saved args mem sp
  have room := pre.room
  have wNat : w.toNat = sp.toNat - 264 := subNat (k := 264) (n := 264) rfl (by omega)
  have wRoom : 9 ≤ w.toNat := by omega
  have wLow : w.toNat + 208 ≤ 2^64 := by have := sp.isLt; omega
  have w8 : w - 8 = sp - 272 := by dsimp only [w]; bv_omega
  have w9 : w - 9 = sp - 273 := by dsimp only [w]; bv_omega
  have wDst : w + 208 = sp - 56 := by dsimp only [w]; bv_omega
  have workWithin : RegionsWithin [⟨(w - 9).toNat,217⟩] [⟨(sp - 273).toNat,273⟩] := by
    rw [w9]
    exact singleWithin (Nat.le_refl _) (Nat.add_le_add_left (by decide : 217 ≤ 273) _)
  have scratchWithin : RegionsWithin [⟨(w - 9).toNat,9⟩] [⟨(w - 9).toNat,217⟩] :=
    singleWithin (Nat.le_refl _) (Nat.add_le_add_left (by decide : 9 ≤ 217) _)
  have savedFrame : RamWriteFrame mem ms [⟨(sp - 273).toNat,273⟩] := saved_frame args mem sp room
  have scratch {m : Ram} (hf : RamWriteFrame mem m [⟨(sp - 273).toNat,273⟩]) :
      Writable code m (w - 9) 9 := by
    rw [w9]
    exact (pre.stack.of_frame hf).sub (Nat.le_refl _) (Nat.add_le_add_left (by decide : 9 ≤ 273) _)
  obtain ⟨r₁, step₁, bit₁, rsp₁, bx₁, bp₁, r12₁, r13₁, r14₁, r15₁, kept₁⟩ :=
    firstChoice code args mem sp x pre.rsp pre.rsi pre.stack pre.inputX
      (fun v hv => cover v (code_l11f780 v hv))
  rw [← w8] at step₁ rsp₁
  have loadX := loadInput (saved_frame args mem sp room) room pre.inputX pre.apartX
  have loadX0 : memLoad (saved args mem sp) x 64 = memLoad mem x 64 := by
    have h := loadX 0 (by decide)
    rw [show x + (0 : Word) = x from BitVec.add_zero x] at h
    exact h
  simp only [loadX0, loadX 8 (by decide), loadX 16 (by decide), loadX 24 (by decide)]
    at bit₁ bp₁ r12₁ r13₁ r14₁ r15₁
  change r₁[7].get 64 = BitVec.ofNat 64 (invalid cx.a cx.b cx.c cx.d).toNat at bit₁
  rw [invalidValid] at bit₁
  obtain ⟨a₂, m₂, reachX, sp₂, al₂, writesX, keepX⟩ :=
    resumeCanonical cover false step₁ rsp₁ (scratch savedFrame) wRoom (by decide) bit₁
  have firstWork : RamWriteFrame ms m₂ [⟨(w - 9).toNat,217⟩] :=
    (RamWriteFrame.refl _ _).trans writesX scratchWithin
  have firstFrame := savedFrame.trans firstWork workWithin
  have bx₂ : a₂[3].get 64 = y := by rw [coordinateReg keepX 3 (by decide) (by decide), bx₁, pre.rdx]
  have secondStack : Writable code m₂ (w - 8) 224 := by
    rw [w8]
    exact (pre.stack.of_frame firstFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨r₂, step₃, bit₃, rsp₃, bp₃, bx₃, r12₃, r13₃, r14₃, r15₃, kept₃⟩ :=
    secondChoice code a₂ m₂ w y sp₂ bx₂ secondStack (pre.inputY.of_frame firstFrame)
      (fun v hv => cover v (code_l11f831 v hv))
  simp only [al₂, bit8, coordinateReg keepX 5 (by decide) (by decide),
    coordinateReg keepX 12 (by decide) (by decide), coordinateReg keepX 13 (by decide) (by decide),
    coordinateReg keepX 14 (by decide) (by decide), coordinateReg keepX 15 (by decide) (by decide),
    bp₁, r12₁, r13₁, r14₁, r15₁]
    at step₃ bit₃ bx₃ r12₃ r13₃ r14₃ r15₃
  change program.runBlock (dialect code) ⟨.l11f831,a₂,m₂⟩ =
    .call ⟨.l127d50,r₂,memStore (coordinateStore m₂ w cx) (w - 8) (0x11f8ea : Word)⟩
      (choiceResume .l11f8ea 0x11f8ea rfl) at step₃
  let mp := coordinatePrefix m₂ w cx
  let mq := coordinateMiddle m₂ w cx
  let mc := coordinateStore m₂ w cx
  let sy : CoordinateWords := ⟨bswapSpec (memLoad mp y 64),
    bswapSpec (memLoad mp (y + 8) 64), bswapSpec (memLoad mp (y + 16) 64),
    bswapSpec (memLoad mq (y + 24) 64)⟩
  change r₂[7].get 64 = BitVec.ofNat 64 (invalid sy.a sy.b sy.c sy.d).toNat at bit₃
  change r₂[3].get 64 = shldResult 36 sy.a sy.b at bx₃
  change r₂[12].get 64 = shldResult 24 sy.b sy.c at r12₃
  change r₂[13].get 64 = shldResult 12 sy.c sy.d &&& 0xfffffffffffff at r13₃
  change r₂[14].get 64 = sy.a >>> 16 at r14₃
  change r₂[15].get 64 = sy.d &&& 0xfffffffffffff at r15₃
  have loadY := loadInput (firstFrame.trans (coordinatePrefixFrame m₂ w cx wRoom wLow) workWithin)
    room pre.inputY pre.apartY
  have loadY0 : memLoad mp y 64 = memLoad mem y 64 := by
    have h := loadY 0 (by decide)
    rw [show y + (0 : Word) = y from BitVec.add_zero y] at h
    exact h
  have loadY24 := loadInput (firstFrame.trans (coordinateMiddleFrame m₂ w cx wRoom wLow) workWithin)
    room pre.inputY pre.apartY 24 (by decide)
  have yEq : sy = cy := by
    dsimp only [sy, cy, readCoordinate]
    rw [loadY0, loadY 8 (by decide), loadY 16 (by decide), loadY24]
  rw [yEq, invalidValid] at bit₃
  rw [yEq] at bx₃ r12₃ r13₃ r14₃ r15₃
  have storeFrame := coordinateStoreFrame m₂ w cx wRoom wLow
  have beforeThird := firstFrame.trans storeFrame workWithin
  obtain ⟨a₄, m₄, reachY, sp₄, al₄, lastScratch, keepY⟩ :=
    resumeCanonical cover true step₃ rsp₃ (scratch beforeThird) wRoom (by decide) bit₃
  have work := ((firstWork.trans storeFrame (singleWithin (Nat.le_refl _) (Nat.le_refl _))).trans
    lastScratch scratchWithin)
  have loadScratch (off : Word) (h : off.toNat + 8 ≤ 208) :
      memLoad m₄ (w + off) 64 = memLoad mc (w + off) 64 := by
    apply lastScratch.memLoad_eq
    have addr : (w + off).toNat = w.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
    rcases List.mem_singleton.mp hr with rfl
    right
    change (w - 9).toNat + 9 ≤ (w + off).toNat
    rw [subNat (k := 9) (n := 9) rfl wRoom, addr]
    omega
  have loadSaved (off : Word) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 56) :
      memLoad m₄ (sp - off) 64 = memLoad ms (sp - off) 64 := by
    apply work.memLoad_eq
    have addr : (sp - off).toNat = sp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    refine ⟨by rw [addr]; have := sp.isLt; omega, fun r hr => ?_⟩
    rcases List.mem_singleton.mp hr with rfl
    right
    change (w - 9).toNat + 217 ≤ (sp - off).toNat
    rw [w9, subNat (k := 273) (n := 273) rfl room, addr]
    omega
  obtain ⟨savedWords, savedDst⟩ := savedSlots args mem sp
  refine ⟨a₄, m₄, reachX.trans reachY, ?_⟩
  refine ⟨sp₄, al₄ ▸ lowBit cy.valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    savedFrame.trans work workWithin⟩
  · rw [coordinateReg keepY 15 (by decide) (by decide), r15₃]
  · rw [coordinateReg keepY 13 (by decide) (by decide), r13₃]
  · rw [coordinateReg keepY 12 (by decide) (by decide), r12₃]
  · rw [coordinateReg keepY 3 (by decide) (by decide), bx₃]
  · rw [coordinateReg keepY 14 (by decide) (by decide), r14₃]
  · rw [coordinateReg keepY 5 (by decide) (by decide), bp₃]
  · change localLimbs m₄ w false = cx.masked
    rw [← coordinateStoreLimbs m₂ w cx]
    apply Vector.ext
    intro i hi
    simp only [localLimbs, Vector.getElem_ofFn]
    apply loadScratch
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact (loadScratch 200 (by decide)).trans (coordinateStoreFlag m₂ w cx)
  · rw [← show w + 208 = sp - 264 + 208 from rfl, wDst, loadSaved 56 (by decide) (by decide)]
    exact savedDst.trans pre.rdi
  · unfold SavedWords at savedWords ⊢
    simpa only [loadSaved 48 (by decide) (by decide), loadSaved 40 (by decide) (by decide),
      loadSaved 32 (by decide) (by decide), loadSaved 24 (by decide) (by decide),
      loadSaved 16 (by decide) (by decide), loadSaved 8 (by decide) (by decide)]
      using savedWords
  · intro i hi
    exact (keepY i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      ((kept₃ i hi).trans ((keepX i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
        (kept₁ i hi)))

end K256.Proofs.Sec1.Affine.Uncompressed
