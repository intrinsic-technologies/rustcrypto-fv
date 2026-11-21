import K256.Proofs.Signing.Composition.Wrapper.Frame
import K256.Proofs.Signing.Composition.Wrapper.Install.Block
import K256.Proofs.Sec1.Parser.Result.Copy

namespace K256.Proofs.Signing.Composition.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

open Install

private theorem preparedWords (q : BitVec 64) (m : Ram) (words : Vector (BitVec 64) 4) :
    WordsAt (scratch q (cleared q (staged q m words))) (q+320) 64 words := by
  intro i hi
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals
    simp (disch := store_disch) only [scratch,cleared,staged,storeWord,wordAddr,Nat.reduceDiv,
      Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,
      memLoad_memStore_same,memLoad_memStore_of_rangeApart]

private theorem copiedWords {q : BitVec 64} {m : Ram} {words : Vector (BitVec 64) 4}
    (h : WordsAt m (q+320) 64 words) : WordsAt (copied q m) (q+200) 64 words := by
  intro i hi
  have fit : 8 * i + 64 / 8 ≤ 120 := by omega
  change memLoad (memCopy (memCopy m (q+80) (q+320) 120) (q+200) (q+80) 120)
    (q+200 + BitVec.ofNat 64 (8*i)) 64 = words[i]
  rw [Sec1.Parser.Result.memLoad_memCopy (off := 8*i) _ _ _ (by decide) fit,
    Sec1.Parser.Result.memLoad_memCopy (off := 8*i) _ _ _ (by decide) fit]
  exact h i hi

private theorem finishedWords (q msg len : BitVec 64) {m : Ram} {words : Vector (BitVec 64) 4}
    (h : WordsAt m (q+200) 64 words) : WordsAt (finished q msg len m) (q+200) 64 words := by
  intro i hi
  have orig := h i hi
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals
    simpa (disch := store_disch) only [finished,storeWord,wordAddr,Nat.reduceDiv,
      Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,
      memLoad_memStore_of_rangeApart] using orig

private theorem finishFrame {q : BitVec 64} {m : Ram} {msg len : BitVec 64}
    (low : 8 ≤ q.toNat) (high : q.toNat + 440 < 2^32) (words : Vector (BitVec 64) 4) :
    RamWriteFrame m (finished q msg len (copied q (scratch q (cleared q (staged q m words)))))
      [⟨(q-8).toNat,448⟩] := by
  let rs : List MemoryRegion := [⟨(q-8).toNat,448⟩]
  have slot : (q-8).toNat = q.toNat-8 := by
    exact BitVec.toNat_sub_of_le (by change 8 ≤ q.toNat; exact low)
  have within (offset size : Nat) (fit : offset+size ≤ 440) :
      InRegions rs (q + BitVec.ofNat 64 offset) size := by
    have ptr : (q + BitVec.ofNat 64 offset).toNat = q.toNat + offset := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨_,List.mem_singleton_self _, ?_⟩
    change (q-8).toNat ≤ _ ∧ _ + size ≤ (q-8).toNat+448 ∧ _ + size ≤ 2^64
    rw [ptr,slot]
    omega
  have put {t : Ram} (h : RamWriteFrame m t rs) (off : Nat) (v : BitVec 64)
      (fit : off+8 ≤ 440) : RamWriteFrame m (storeWord t q off v) rs :=
    h.memStore v (within off 8 fit)
  have prep : RamWriteFrame m (scratch q (cleared q (staged q m words))) rs := by
    unfold scratch cleared staged
    repeat apply put
    all_goals first | exact .refl _ _ | decide
  have firstCopy := Sec1.Wrapper.Copy.memCopy_frame (src := q+320) prep (within 80 120 (by decide))
  have secondCopy : RamWriteFrame m (copied q (scratch q (cleared q (staged q m words)))) rs :=
    Sec1.Wrapper.Copy.memCopy_frame (src := q+80) firstCopy (within 200 120 (by decide))
  have tail := put (put secondCopy 320 msg (by decide)) 328 len (by decide)
  unfold finished
  apply tail.memStore
  refine ⟨_,List.mem_singleton_self _,Nat.le_refl _,?_,?_⟩
  · change (q-8).toNat+8 ≤ (q-8).toNat+448
    omega
  · change (q-8).toNat+8 ≤ 2^64
    rw [slot]
    omega

set_option maxHeartbeats 1200000 in
theorem install {s : RamState} {secret msg : ByteArray} {d : Nat} {a : Registers} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (entry : Decoded s d a m) :
    ∃ b n, Reach (atBlock .l1026a6 a m) (core .l105420 b n) ∧ CoreEntry s d msg b n := by
  let q := localSp s
  let words := scalarWords d
  obtain ⟨room,high,_⟩ := stackBounds call
  have qNat : q.toNat = (stackPtr s).toNat-472 := by
    rw [show q = stackPtr s - 472 from localSp_eq s]
    exact Common.stackOffset (off := 472) call.stackAvailable (by decide)
  have slotAddr : q-8 = stackPtr s - 480 := by rw [show q = _ from localSp_eq s]; bv_omega
  have slotNat : (q-8).toNat = (stackPtr s).toNat-480 := by
    rw [slotAddr]
    exact Common.stackOffset (off := 480) call.stackAvailable (by decide)
  have win : Writable Extracted.programImage m (q-8) 480 := by
    rw [slotAddr]
    exact (Common.stackWritable (off := 480) call (by decide) (by decide) (by decide)).of_frame entry.written
  have key (i : Nat) (hi : i < 4) :
      memLoad m (wordAddr (q+40) 64 i) 64 = words[i] :=
    entry.key i hi
  have word1 : memLoad m (q+48) 64 = words[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
      using key 1 (by decide)
  have word2 : memLoad m (q+56) 64 = words[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
      using key 2 (by decide)
  have word3 : memLoad m (q+64) 64 = words[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
      using key 3 (by decide)
  obtain ⟨b,run,rsp,dst,src,desc,count,keep⟩ := finishBlock (m := m) (q := q) (words := words)
    win (by omega) (by omega)
    (by rw [entry.rsp,Value.get_mk])
    (by rw [entry.df,Value.get_mk])
    (by rw [entry.message,Value.get_mk])
    (by rw [entry.length,Value.get_mk])
    (by simpa only [wordAddr,Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using key 0 (by decide))
    word1 word2 word3
  let n := finished q (s.regValue .rdx) (s.regValue .rcx) (copied q (scratch q (cleared q (staged q m words))))
  have frame : RamWriteFrame m n [⟨(q-8).toNat,448⟩] :=
    finishFrame (by omega) (by omega) words
  have memory := preserveSlots call entry.toMemory frame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (q-8).toNat ∧ (q-8).toNat+448 ≤ _
    omega)
  have address (offset : Nat) :
      q + BitVec.ofNat 64 offset = sp s + BitVec.ofNat 64 (816+offset) := by
    change sp s + 816 + _ = _
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have secretAddr : q + 200 = sp s+1016 := address 200
  have resultAddr : q + 72 = sp s+888 := address 72
  have descriptorAddr : q + 320 = sp s+1136 := address 320
  have lengthAddr : q + 328 = sp s+1144 := address 328
  have keyOut : WordsAt n (sp s+1016) 64 words := by
    rw [← secretAddr]
    exact finishedWords q _ _ (copiedWords (preparedWords q m words))
  have ret : memLoad n (sp s+808) 64 = 0x102795 := by
    change memLoad n (sp s+808) 64 = _
    rw [show sp s+808 = q-8 by change sp s+808 = sp s+816-8; bv_omega]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have msgSize : s.regValue .rcx = BitVec.ofNat 64 msg.size := by
    have length : (s.regValue .rcx).toNat = msg.size := call.lengthArgumentsMatchInputs.2.1
    rw [← length,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have descriptor : Descriptor s msg n := by
    constructor
    · rw [← descriptorAddr]
      dsimp only [n,finished,storeWord]
      simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [← lengthAddr, ← msgSize]
      dsimp only [n,finished,storeWord]
      simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  refine ⟨b,n,?_,⟨⟨memory,keyOut,ret⟩,descriptor,?_,?_,?_,?_,count,
    (keep 3 (by decide)).trans entry.output,(keep 5 (by decide)).trans entry.rbp,
    (keep 13 (by decide)).trans entry.r13,(keep 22 (by decide)).trans entry.df,?_,?_⟩⟩
  · exact Semantics.Reaches.single (congrArg (Transfer.next (dialect Extracted.programImage) []) run)
  · rw [← show q-8 = sp s+808 by change sp s+816-8 = _; bv_omega]
    exact rsp
  · rw [← resultAddr]
    exact dst
  · rw [← secretAddr]
    exact src
  · rw [← descriptorAddr]
    exact desc
  · rintro ⟨i,hi⟩ isSaved
    simp only [List.mem_cons,List.not_mem_nil,or_false] at isSaved
    rcases isSaved with rfl|rfl|rfl
    · exact (congrArg Value.width (keep 12 (by decide))).trans entry.r12
    · exact congrArg Value.width ((keep 14 (by decide)).trans entry.length)
    · exact congrArg Value.width ((keep 15 (by decide)).trans entry.message)
  · exact ⟨(congrArg Value.width (keep 39 (by decide))).trans entry.fp.1,
        (congrArg Value.width (keep 50 (by decide))).trans entry.fp.2.1,
        (congrArg Value.width (keep 51 (by decide))).trans entry.fp.2.2⟩

end K256.Proofs.Signing.Composition.Wrapper
