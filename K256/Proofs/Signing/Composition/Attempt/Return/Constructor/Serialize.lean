import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.State
import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Signing.LIR.Functions2
import K256.Proofs.Signing.LIR.Fn103450
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.WordCopy
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Wrapper.Scalar.Blocks

namespace K256.Proofs.Signing.Composition.Attempt.Return.Constructor

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.DomainParameters.Secp256k1
open Signing.LIR
open Verify.Core (Registers)
open Generate.Wrapper (writeScalarWords)
open Generate.Generator.Multiply (scalarWords)

private theorem serializeBlock {code : CodeMap} {a : Vector Value Reg.count} {mem : Ram}
    {src dst sp retAddr : BitVec 64} {word : Nat → BitVec 64}
    (rsp : a[4].get 64 = sp) (rsi : a[6].get 64 = src) (rdi : a[7].get 64 = dst)
    (load : ∀ i < 4, LoadOk mem (wordAddr src 64 i) 8)
    (words : ∀ i < 4, bswapSpec (memLoad mem (wordAddr src 64 (3 - i)) 64) = word i)
    (store₀ : StoreOk code mem dst 8 0x11c3de 3)
    (store₁ : StoreOk code (writeScalarWords dst word mem 1) (dst + 8) 8 0x11c3e1 4)
    (store₂ : StoreOk code (writeScalarWords dst word mem 2) (dst + 16) 8 0x11c3e5 4)
    (store₃ : StoreOk code (writeScalarWords dst word mem 3) (dst + 24) 8 0x11c3e9 4)
    (retOk : LoadOk (writeScalarWords dst word mem 4) sp 8)
    (ret : memLoad (writeScalarWords dst word mem 4) sp 64 = retAddr)
    (retLow : retAddr.toNat < 2^32) :
    ∃ out, program.runBlock (dialect code) ⟨.l11c3c0, a, mem⟩ = .returned out ∧
      out.tag = some ⟨64, retAddr⟩ ∧ out.store = writeScalarWords dst word mem 4 ∧
      out.values[4] = ⟨64, sp + 8⟩ ∧
      (out.values[1].width = 64 ∧ out.values[2].width = 64 ∧
        out.values[6].width = 64 ∧ out.values[7].width = 64) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] → out.values[i] = a[i]) := by
  have ld₀ : LoadOk mem src 8 := by
    have h := load 0 (by decide)
    rwa [show wordAddr src 64 0 = src from BitVec.add_zero src] at h
  have ld₁ : LoadOk mem (src + 8) 8 := load 1 (by decide)
  have ld₂ : LoadOk mem (src + 16) 8 := load 2 (by decide)
  have ld₃ : LoadOk mem (src + 24) 8 := load 3 (by decide)
  have w₀ : bswapSpec (memLoad mem (src + 24) 64) = word 0 := words 0 (by decide)
  have w₁ : bswapSpec (memLoad mem (src + 16) 64) = word 1 := words 1 (by decide)
  have w₂ : bswapSpec (memLoad mem (src + 8) 64) = word 2 := words 2 (by decide)
  have w₃ : bswapSpec (memLoad mem src 64) = word 3 := by
    have h := words 3 (by decide)
    change bswapSpec (memLoad mem (wordAddr src 64 0) 64) = word 3 at h
    rwa [show wordAddr src 64 0 = src from BitVec.add_zero src] at h
  have zeroAddr : wordAddr dst 64 0 = dst := BitVec.add_zero dst
  have addr₁ : wordAddr dst 64 1 = dst + 8 := rfl
  have addr₂ : wordAddr dst 64 2 = dst + 16 := rfl
  have addr₃ : wordAddr dst 64 3 = dst + 24 := rfl
  simp only [writeScalarWords, zeroAddr, addr₁, addr₂, addr₃] at store₁ store₂ store₃ retOk ret
  refine ⟨?out, ?eval, ?tag, ?memory, ?stack, ?widths, ?kept⟩
  case eval =>
    cfg_eval
    simp only [rsp, rsi, rdi, ld₀, ld₁, ld₂, ld₃, w₀, w₁, w₂, w₃, store₀,
      store₁, store₂, store₃, retOk, ret, retLow, and_self, ↓reduceIte]
    rfl
  case tag => rfl
  case memory => simp only [writeScalarWords, zeroAddr, addr₁, addr₂, addr₃]
  case stack => rfl
  case widths => exact ⟨rfl,rfl,rfl,rfl⟩
  case kept =>
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem get64 {a : Registers} {i : Nat} {hi : i < Reg.count} {w : BitVec 64}
    (h : a[i] = ⟨64,w⟩) : a[i].get 64 = w := by
  rw [h]
  rfl

private def firstMemory (p : BitVec 64) (m : Ram) : Ram :=
  memStore (memStore (memStore (memStore m (p+216) (p+688))
    (p+208) (p+392)) (p+200) (p+688)) p (0x103472 : BitVec 64)

private theorem keptBySerializer {i : Nat} (hi : i ∈ [5,8,9,12,13,22,39,50,51]) :
    i ∈ [3,5,8,9,12,13,14,15,22,39,50,51] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
  omega

private theorem keptRegs {a b : Registers} (h : ∀ i : Fin Reg.count,
    i.val ∈ [5,8,9,12,13,22,39,50,51] → b[i] = a[i]) :
    b[5] = a[5] ∧ b[8] = a[8] ∧ b[9] = a[9] ∧ b[12] = a[12] ∧ b[13] = a[13] ∧
      b[22] = a[22] ∧ b[39] = a[39] ∧ b[50] = a[50] ∧ b[51] = a[51] :=
  ⟨h 5 (by decide), h 8 (by decide), h 9 (by decide), h 12 (by decide), h 13 (by decide),
    h 22 (by decide), h 39 (by decide), h 50 (by decide), h 51 (by decide)⟩

set_option maxHeartbeats 1000000 in
private theorem firstBlock {p : BitVec 64} {a : Registers} {m : Ram}
    (area : Writable Extracted.programImage m p 720)
    (rsp : a[4].get 64 = p+224) (dst : a[7].get 64 = p+240)
    (first : a[6] = ⟨64,p+392⟩) (second : a[2].get 64 = p+688)
    (r14 : a[14].get 64 = p+392) (r15 : a[15].get 64 = p+688)
    (bx : a[3].get 64 = p+688) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l103450,a,m⟩ =
        .call ⟨.l11c3c0,b,firstMemory p m⟩ (resume .l103472 0x103472) ∧
      b[4] = ⟨64,p⟩ ∧ b[6] = ⟨64,p+392⟩ ∧ b[7] = ⟨64,p+136⟩ ∧
      b[3] = ⟨64,p+240⟩ ∧ b[14] = ⟨64,p+688⟩ ∧ b[15] = ⟨64,p+136⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,8,9,12,13,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?args,?run,?_,?_,?_,?_,?_,?_,?_⟩
  case run =>
    cfg_eval [rsp,dst,second,r14,r15,bx,BitVec.add_assoc,BitVec.reduceAdd,Lift.reduceAddOffset]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l103450)
    rfl
  all_goals try rfl
  · exact first
  · rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private def secondMemory (p : BitVec 64) (initial : Ram) : Ram :=
  let m := memStore initial (p+88) (memLoad initial (p+32) 64)
  let m := memStore m (p+96) (memLoad initial (p+40) 64)
  let m := memStore m (p+72) (memLoad initial (p+16) 64)
  let m := memStore m (p+80) (memLoad initial (p+24) 64)
  let m := memStore m (p+160) (memLoad initial (p+712) 64)
  let m := memStore m (p+152) (memLoad initial (p+704) 64)
  let m := memStore m (p+144) (memLoad initial (p+696) 64)
  let m := memStore m (p+136) (memLoad initial (p+688) 64)
  memStore m p (0x1034fb : BitVec 64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem secondBlock {p : BitVec 64} {a : Registers} {m : Ram}
    (area : Writable Extracted.programImage m p 720)
    (rsp : a[4].get 64 = p+8) (src : a[14].get 64 = p+688) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l10348c,a,m⟩ =
        .call ⟨.l11c3c0,b,secondMemory p m⟩ (resume .l1034fb 0x1034fb) ∧
      b[4] = ⟨64,p⟩ ∧ b[6] = ⟨64,p+136⟩ ∧ b[7] = ⟨64,p+168⟩ ∧
      b[3] = a[3] ∧ b[14] = ⟨64,p+168⟩ ∧ b[15] = a[15] ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,8,9,12,13,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?args,?run,?_,?_,?_,?_,?_,?_,?_⟩
  case run =>
    cfg_eval [rsp,src,BitVec.add_assoc,BitVec.reduceAdd,Lift.reduceAddOffset]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10348c)
    segment_words [BitVec.add_assoc, BitVec.reduceAdd]
    unfold secondMemory
    rfl
  all_goals try rfl
  · rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private def serialized (dst : BitVec 64) (x : Nat) (m : Ram) : Ram :=
  writeScalarWords dst (fun i => bswapSpec ((scalarWords x)[3-i]'(by omega))) m 4

private theorem serializedWords {dst : BitVec 64} {x : Nat} {m : Ram} :
    ∀ i (hi : i < 4), Common.scalarWord (serialized dst x m) dst i = (scalarWords x)[i] := by
  intro i hi
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  all_goals simp (disch := first | decide | store_disch) only [serialized, writeScalarWords,
    Common.scalarWord, wordAddr, Nat.reduceDiv, Nat.reduceSub, Nat.reduceMul,
    BitVec.add_zero, memLoad_memStore_of_rangeApart, memLoad_memStore_same, Common.bswapSpec_bswapSpec]

private theorem window {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (mem : Memory s m) :
    Writable Extracted.programImage m (sp s-232) 720 := by
  rw [addr_sub]
  exact stackWindow call mem (by decide)

private theorem workSlot {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {off : BitVec 64}
    (bound : off.toNat + 8 ≤ 576) :
    InRegions (workRegions s) (sp s-232+off) 8 := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have lower : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have p : (sp s-232).toNat = (sp s).toNat-232 := belowNat call (by decide)
  refine ⟨_, List.mem_cons_self, ?_⟩
  change (sp s-9904).toNat ≤ _ ∧ _ + 8 ≤ (sp s-9904).toNat + 10248 ∧ _ + 8 ≤ 2^64
  rw [BitVec.toNat_add, p, lower, Nat.mod_eq_of_lt (by omega : (sp s).toNat-232+off.toNat < 2^64)]
  omega

private theorem serializedFrame {m : Ram} {dst : BitVec 64} {x : Nat} {regions : List MemoryRegion}
    (slot : ∀ i < 4, InRegions regions (wordAddr dst 64 i) 8) :
    RamWriteFrame m (serialized dst x m) regions := by
  unfold serialized
  simp only [writeScalarWords]
  iterate 4 refine RamWriteFrame.memStore ?_ _ (slot _ (by decide))
  exact .refl _ _

set_option maxHeartbeats 1200000 in
private theorem serializeAt {p to source retAddr : BitVec 64} {x : Nat} {a : Registers} {m : Ram}
    (rsp : a[4] = ⟨64,p⟩) (src : a[6] = ⟨64,source⟩) (dst : a[7] = ⟨64,to⟩)
    (read : Readable m source 32) (write : Writable Extracted.programImage m to 32)
    (stack : Readable m p 8) (ret : memLoad m p 64 = retAddr) (low : retAddr.toNat < 2^32)
    (apart : ∀ i < 4, RangeApart p 8 (wordAddr to 64 i) 8)
    (words : WordsAt m source 64 (scalarWords x)) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l11c3c0,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,retAddr⟩ ∧ out.store = serialized to x m ∧ out.values[4] = ⟨64,p+8⟩ ∧
      (out.values[1].width = 64 ∧ out.values[2].width = 64 ∧
        out.values[6].width = 64 ∧ out.values[7].width = 64) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) := by
  let word (i : Nat) := bswapSpec ((scalarWords x)[3-i]'(by omega))
  have load (i : Nat) (hi : i < 4) : LoadOk m (wordAddr source 64 i) 8 := by
    apply LoadOk.of_offsets read rfl (addr_self source)
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals decide
  have swap (i : Nat) (hi : i < 4) :
      bswapSpec (memLoad m (wordAddr source 64 (3-i)) 64) = word i := by
    exact congrArg bswapSpec (words (3-i) (by omega))
  have retOk : LoadOk (serialized to x m) p 8 := by
    unfold serialized
    simp only [writeScalarWords]
    slot_guard using code_l11c3c0
  have retWord : memLoad (serialized to x m) p 64 = retAddr := by
    have sep (i : Nat) (hi : i < 4) : RangeApart (wordAddr to 64 i) 8 p 8 :=
      fun j hj k hk eq => apart i hi k hk j hj eq.symm
    simp only [serialized, writeScalarWords]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (sep 3 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (sep 2 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (sep 1 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (sep 0 (by decide))]
    exact ret
  have store₀ : StoreOk Extracted.programImage m to 8 0x11c3de 3 := by
    slot_guard using code_l11c3c0
  have store₁ : StoreOk Extracted.programImage (writeScalarWords to word m 1) (to + 8) 8 0x11c3e1 4 := by
    simp only [writeScalarWords]
    slot_guard using code_l11c3c0
  have store₂ : StoreOk Extracted.programImage (writeScalarWords to word m 2) (to + 16) 8 0x11c3e5 4 := by
    simp only [writeScalarWords]
    slot_guard using code_l11c3c0
  have store₃ : StoreOk Extracted.programImage (writeScalarWords to word m 3) (to + 24) 8 0x11c3e9 4 := by
    simp only [writeScalarWords]
    slot_guard using code_l11c3c0
  exact serializeBlock (get64 rsp) (get64 src) (get64 dst) load swap store₀ store₁ store₂ store₃
    retOk retWord low

private theorem returnStep {lab : Label} {retAddr : BitVec 64} {a : Registers} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : program.runBlock (dialect Extracted.programImage) ⟨.l11c3c0,a,m⟩ = .returned out)
    (tag : out.tag = some ⟨64,retAddr⟩) :
    Reach ⟨⟨.l11c3c0,a,m⟩, resume lab retAddr :: (inside lab a m).stack⟩
      (inside lab out.values out.store) := by
  refine .single ?_
  change (program.runBlock (dialect Extracted.programImage) ⟨.l11c3c0,a,m⟩).next
    (dialect Extracted.programImage) (resume lab retAddr :: (inside lab a m).stack) = _
  rw [run]
  have loc : (resume lab retAddr).resume out = (⟨lab,out.values,out.store⟩ : lifted.Location) :=
    congrArg (fun args => (⟨lab,args,out.store⟩ : lifted.Location))
      (ParseSignature.resume_arguments (resume lab retAddr) out)
  have accepts : (resume lab retAddr).Accepts (dialect Extracted.programImage) out.tag = true := by
    rw [tag]
    simp [StackFrame.Accepts, dialect]
  simp only [Transfer.next, accepts, ↓reduceIte, loc]
  rfl

private theorem resultWidths {a b : Registers}
    (w8 : a[8].width = 64) (w9 : a[9].width = 64)
    (new : b[1].width = 64 ∧ b[2].width = 64 ∧ b[6].width = 64 ∧ b[7].width = 64)
    (r8 : b[8] = a[8]) (r9 : b[9] = a[9]) : ParseSignature.ArgumentWidths b := by
  rcases new with ⟨c,d,s,t⟩
  have w8 : b[8].width = 64 := (congrArg Value.width r8).trans w8
  have w9 : b[9].width = 64 := (congrArg Value.width r9).trans w9
  rintro ⟨i,hi⟩ member
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

private theorem serializeWindow {p src dst retAddr : BitVec 64} {x : Nat} {a : Registers} {m : Ram}
    (area : Writable Extracted.programImage m p 720)
    (rsp : a[4] = ⟨64,p⟩) (rsi : a[6] = ⟨64,p+src⟩) (rdi : a[7] = ⟨64,p+dst⟩)
    (srcIn : (src-0).toNat + 32 ≤ 720) (dstIn : (dst-0).toNat + 32 ≤ 720)
    (separate : 8 ≤ (dst-0).toNat ∧ 32 ≤ (0-dst).toNat)
    (ret : memLoad m p 64 = retAddr) (low : retAddr.toNat < 2^32)
    (words : WordsAt m (p+src) 64 (scalarWords x)) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l11c3c0,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,retAddr⟩ ∧ out.store = serialized (p+dst) x m ∧ out.values[4] = ⟨64,p+8⟩ ∧
      (out.values[1].width = 64 ∧ out.values[2].width = 64 ∧
        out.values[6].width = 64 ∧ out.values[7].width = 64) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) := by
  have readSrc : Readable m (p+src) 32 := area.readable.of_offsets
    (rfl : p+src = p+src) (addr_self p) srcIn
  have writeDst : Writable Extracted.programImage m (p+dst) 32 := area.of_offsets
    (rfl : p+dst = p+dst) (addr_self p) dstIn
  have adj : RangeApart p 8 (p+dst) 32 :=
    RangeApart.of_offsets (addr_self p) rfl separate
  exact serializeAt rsp rsi rdi readSrc writeDst (area.readable.sub (by omega) (by omega)) ret low
    (fun i hi => Refine.RangeApart.right_sub adj (off := 8*i) (by omega)) words

private theorem callStep {start lab : Label} {retAddr : BitVec 64} {a b : Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨start,a,m⟩ =
      .call ⟨.l11c3c0,b,n⟩ (resume lab retAddr)) :
    Reach (inside start a m) ⟨⟨.l11c3c0,b,n⟩, resume lab retAddr :: (inside lab a m).stack⟩ :=
  .single (congrArg (Transfer.next (dialect Extracted.programImage) (inside start a m).stack) run)

private theorem firstFrame {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RamWriteFrame m (firstMemory (sp s-232) m) (workRegions s) := by
  unfold firstMemory
  iterate 4 refine RamWriteFrame.memStore ?_ _ ?_
  · exact .refl _ _
  all_goals
    first
    | exact workSlot call (by decide)
    | have zero : sp s-232+(0 : BitVec 64) = sp s-232 := BitVec.add_zero _
      exact zero ▸ workSlot call (off := 0) (by decide)

private theorem secondFrame {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RamWriteFrame m (secondMemory (sp s-232) m) (workRegions s) := by
  dsimp only [secondMemory]
  iterate 9 refine RamWriteFrame.memStore ?_ _ ?_
  · exact .refl _ _
  all_goals
    first
    | exact workSlot call (by decide)
    | have zero : sp s-232+(0 : BitVec 64) = sp s-232 := BitVec.add_zero _
      exact zero ▸ workSlot call (off := 0) (by decide)

local macro "constructor_words" : tactic =>
  `(tactic| (
    simp only [serialized, writeScalarWords, firstMemory, secondMemory, wordAddr, Nat.reduceDiv,
      Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
    simp (disch := first | decide | exact RangeApart.of_offsets rfl rfl (by decide) |
      exact RangeApart.of_offsets (addr_self _) rfl (by decide)) only
      [memLoad_memStore_same, memLoad_memStore_of_rangeApart]))

private theorem encodedFrame {s : RamState} {secret msg : ByteArray} {x : Nat} {m : Ram} {off : BitVec 64}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (inside : off.toNat + 32 ≤ 576) :
    RamWriteFrame m (serialized (sp s-232+off) x m) (workRegions s) := by
  apply serializedFrame
  intro i hi
  have eq : wordAddr (sp s-232+off) 64 i = sp s-232+(off+BitVec.ofNat 64 (8*i)) := by
    change sp s-232+off+BitVec.ofNat 64 (8*i) = _
    rw [BitVec.add_assoc]
  rw [eq]
  apply workSlot call
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*i < 2^64),
    Nat.mod_eq_of_lt (by omega : off.toNat+8*i < 2^64)]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem first {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {st : State} {r sigS : Nat} {a : Registers} {m : Ram}
    (input : Entry s d msg st r sigS a m) :
    ∃ b n, Reach (inside .l103450 a m) (inside .l103472 b n) ∧
      Active s d msg st false r sigS b n ∧ encoded s false n r := by
  let p := sp s-232
  have adds (i : BitVec 64) : sp s+i = p+(232+i) := by dsimp only [p]; bv_omega
  have subs (i : BitVec 64) : sp s-i = p+(232-i) := by dsimp only [p]; bv_omega
  have area := window call input.toMemory
  have rsp : a[4].get 64 = p+224 := by simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using get64 input.rsp
  have dst : a[7].get 64 = p+240 := by simpa only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using get64 input.dst
  have src : a[6] = ⟨64,p+392⟩ := by simpa only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using input.first
  have snd : a[2].get 64 = p+688 := by simpa only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using get64 input.second
  have r14 : a[14].get 64 = p+392 := by simpa only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using get64 input.r14
  have r15 : a[15] = ⟨64,p+688⟩ := by
    simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using input.regs.r15
  have bx : a[3] = ⟨64,p+688⟩ := by
    simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using input.regs.rbx
  obtain ⟨b,run,spB,srcB,dstB,bxB,r14B,r15B,kept⟩ :=
    firstBlock area rsp dst src snd r14 (get64 r15) (get64 bx)
  have frame := firstFrame (m := m) call
  have words : WordsAt (firstMemory p m) (p+392) 64 (scalarWords r) := by
    intro i hi
    have h := input.rWords i hi
    rw [adds] at h
    simp only [BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals
      constructor_words
      simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using h
  obtain ⟨out,exec,tag,memory,rspOut,newWidths,preserved⟩ :=
    serializeWindow (area.of_frame frame) spB srcB dstB (by decide) (by decide)
      (by decide) (by unfold firstMemory; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by decide) words
  change out.store = serialized (p+136) r (firstMemory p m) at memory
  have written := frame.trans (encodedFrame (m := firstMemory p m) (x := r) (off := 136) call
    (by decide)) (fun item h => ⟨item,h,Nat.le_refl _,Nat.le_refl _⟩)
  have hkeep (i : Fin Reg.count) (hi : i.val ∈ [5,8,9,12,13,22,39,50,51]) :
      out.values[i] = a[i] := (preserved i (keptBySerializer hi)).trans (kept i hi)
  obtain ⟨bp,r8,r9,r12,r13,df,fp39,fp50,fp51⟩ := keptRegs hkeep
  have w8 : a[8].width = 64 := by
    have h := input.regs.widths ⟨8, by decide⟩ (by decide)
    change ((a.set 4 ⟨64,sp s⟩)[8]).width = 64 at h
    simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using h
  have w9 : a[9].width = 64 := by
    have h := input.regs.widths ⟨9, by decide⟩ (by decide)
    change ((a.set 4 ⟨64,sp s⟩)[9]).width = 64 at h
    simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using h
  have fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16 := by
    simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using input.regs.fp
  refine ⟨out.values,out.store,(callStep run).trans (returnStep exec tag),?_,?_⟩
  · constructor
    · rw [memory]
      exact input.toLoopMemory.preserve_work call written
    · rw [subs]
      exact rspOut
    · exact df.trans (by simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using input.regs.df)
    · rw [adds]
      exact (preserved 3 (by decide)).trans bxB
    · exact bp.trans (by simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using input.regs.rbp)
    · exact r12.trans (by simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using input.regs.r12)
    · exact r13.trans (by simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using input.regs.r13)
    · change out.values[14] = ⟨64,sp s+456⟩
      rw [adds]
      exact (preserved 14 (by decide)).trans r14B
    · rw [subs]
      exact (preserved 15 (by decide)).trans r15B
    · exact resultWidths w8 w9 newWidths r8 r9
    · rw [fp39,fp50,fp51]
      exact fp
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simp only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simp only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simp only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using input.constructorReturn
    · change WordsAt out.store (sp s+456) 64 (scalarWords sigS)
      intro i hi
      rw [memory,adds]
      simp only [BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
      have h := input.sWords i hi
      rw [adds] at h
      simp only [BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h
      obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
      all_goals
      constructor_words
      simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using h
  · change ∀ i (hi : i < 4), Common.scalarWord out.store (sp s-96) i = (scalarWords r)[i]
    rw [memory,subs]
    exact serializedWords

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem second {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {st : State} {r sigS : Nat} {a : Registers} {m : Ram}
    (input : Active s d msg st false r sigS a m)
    (words : WordsAt m (sp s-216) 64 (scalarWords r)) :
    ∃ b n, Reach (inside .l10348c a m) (inside .l1034fb b n) ∧
      Active s d msg st true r sigS b n ∧ encoded s true n sigS := by
  let p := sp s-232
  have adds (i : BitVec 64) : sp s+i = p+(232+i) := by dsimp only [p]; bv_omega
  have subs (i : BitVec 64) : sp s-i = p+(232-i) := by dsimp only [p]; bv_omega
  have area := window call input.toMemory
  have rsp : a[4].get 64 = p+8 := by simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using get64 input.rsp
  have src : a[14].get 64 = p+688 := by simpa only [adds, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using get64 (show a[14] = ⟨64,sp s+456⟩ from input.r14)
  obtain ⟨b,run,spB,srcB,dstB,bxB,r14B,r15B,kept⟩ := secondBlock area rsp src
  have frame := secondFrame (m := m) call
  have srcWords : WordsAt (secondMemory p m) (p+136) 64 (scalarWords sigS) := by
    have other : WordsAt m (sp s+456) 64 (scalarWords sigS) := input.other
    intro i hi
    have h := other i hi
    rw [adds] at h
    simp only [BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals
      constructor_words
      simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using h
  obtain ⟨out,exec,tag,memory,rspOut,newWidths,preserved⟩ :=
    serializeWindow (area.of_frame frame) spB srcB dstB (by decide) (by decide)
      (by decide) (by unfold secondMemory; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by decide) srcWords
  change out.store = serialized (p+168) sigS (secondMemory p m) at memory
  have written := frame.trans (encodedFrame (m := secondMemory p m) (x := sigS) (off := 168) call
    (by decide)) (fun item h => ⟨item,h,Nat.le_refl _,Nat.le_refl _⟩)
  have hkeep (i : Fin Reg.count) (hi : i.val ∈ [5,8,9,12,13,22,39,50,51]) :
      out.values[i] = a[i] := (preserved i (keptBySerializer hi)).trans (kept i hi)
  obtain ⟨bp,r8,r9,r12,r13,df,fp39,fp50,fp51⟩ := keptRegs hkeep
  refine ⟨out.values,out.store,(callStep run).trans (returnStep exec tag),?_,?_⟩
  · constructor
    · rw [memory]
      exact input.toLoopMemory.preserve_work call written
    · rw [subs]
      exact rspOut
    · exact df.trans input.df
    · exact (preserved 3 (by decide)).trans (bxB.trans input.bx)
    · exact bp.trans input.bp
    · exact r12.trans input.r12
    · exact r13.trans input.r13
    · change out.values[14] = ⟨64,sp s-64⟩
      rw [subs]
      exact (preserved 14 (by decide)).trans r14B
    · exact (preserved 15 (by decide)).trans (r15B.trans input.r15)
    · exact resultWidths (input.widths 8 (by decide)) (input.widths 9 (by decide)) newWidths r8 r9
    · rw [fp39,fp50,fp51]
      exact input.fp
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using input.savedBx
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using input.constructor14
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using input.constructor15
    · rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      constructor_words
      simpa only [subs, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using input.constructorReturn
    · change WordsAt out.store (sp s-160) 64 (scalarWords r)
      intro i hi
      rw [memory,subs]
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      have h := words i hi
      rw [subs] at h
      simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat] at h
      obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
      all_goals
      constructor_words
      simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using h
  · change ∀ i (hi : i < 4), Common.scalarWord out.store (sp s-64) i = (scalarWords sigS)[i]
    rw [memory,subs]
    exact serializedWords

end K256.Proofs.Signing.Composition.Attempt.Return.Constructor
