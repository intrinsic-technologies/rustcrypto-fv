import K256.Proofs.Generate.Generator.Multiply.Loop.State
import K256.Proofs.Generate.Generator.Multiply.Records

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private def setupMemory (m : Ram) (sp : BitVec 64) :=
  let m := memStore m (sp + 0x260) (66 : BitVec 64)
  let m := memStore m (sp + 0x268) (66 : BitVec 64)
  let m := memStore m (sp + 0x258) (66 : BitVec 64)
  memStore m (sp + 0x1c8) (0xfffffffffff8 : BitVec 64)

set_option maxHeartbeats 800000 in
private theorem setupBlock {a : Registers} {m : Ram} {sp digits : BitVec 64}
    (rsp : a[4].get 64 = sp)
    (stack : Writable Extracted.programImage m sp 0xc88)
    (count : Readable m (sp + 0xcc0) 8)
    (ptr : memLoad m (sp + 0xf0) 64 = digits)
    (first : memLoad m (sp + 0x100) 64 = 1)
    (second : memLoad m (sp + 0xcc0) 64 = 1)
    (third : memLoad m (sp + 0x1a0) 64 = 1)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a) :
    ∃ b, Reaches .l11d748 a m .l11d7ef b (setupMemory m sp) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
      b[1] = ⟨64,32⟩ ∧ b[2] = ⟨64,digits+64⟩ ∧ b[12].get 64 = sp + 0x490 ∧
      ∀ j : Fin Reg.count, j.val ∈ [4,22,39,50,51] → b[j] = a[j] := by
  refine ⟨?b, ?reach, ?width, ?saved, ?cx, ?dx, ?r12, ?keep⟩
  case reach =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11d748,a,m⟩ =
        .jump ⟨.l11d7ef,?b,setupMemory m sp⟩ := by
      arithmetic_segment using code_l11d748 [rsp,ptr,first,second,third,setupMemory]
    apply Semantics.Reaches.single
    change program.step _ _ = _
    simp only [Program.step, run, Transfer.next]
  case width =>
    rintro ⟨i,hi⟩ hm
    have w := widths ⟨i,hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
  case saved =>
    rintro ⟨i,hi⟩ hm
    have w := saved ⟨i,hi⟩ hm
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
  case keep =>
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl
  all_goals rfl

set_option maxHeartbeats 750000 in
theorem windowSetup {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr initial d) (ready : Prepared fr a m d) :
    ∃ b n, Reaches .l11d748 a m .l11d7ef b n ∧ WindowHead fr b n d 32 := by
  let sp := fr.rsp - 0xcb8
  let m' := setupMemory m sp
  let writes : List MemoryRegion := [⟨(sp+0x1c8).toNat,0xa8⟩]
  have room := entry.room
  have high := entry.high
  have sn : sp.toNat = fr.rsp.toNat - 0xcb8 :=
    BitVec.toNat_sub_of_le (by change 0xcb8 ≤ fr.rsp.toNat; omega)
  have sub (k : BitVec 64) (h : k.toNat ≤ 0xed8) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by change k.toNat ≤ fr.rsp.toNat; omega)
  have add (k : BitVec 64) (h : k.toNat ≤ 6320) :
      (fr.rsp + k).toNat = fr.rsp.toNat + k.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have spAdd (k : BitVec 64) (h : k.toNat ≤ 0xcc0) :
      (sp + k).toNat = sp.toNat + k.toNat := BitVec.toNat_add_of_lt (by omega)
  have atoms := ready.atoms
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp,df,mx,ft,fc,bx,r12,r13,r14,r15,bp,retRead,ret,retLow,stack,low,align,
    gRead1,got1,gRead2,got2,sep,_⟩ := atoms
  have full : Writable Extracted.programImage m sp 0xc88 :=
    stack.sub (by rw [sn,sub _ (by decide)]; change _ - 3800 ≤ _ - 3256; omega)
      (by rw [sn,sub _ (by decide)]; change _ - 3256 + 3208 ≤ _ - 3800 + 3800; omega)
  have cr : Readable m (sp + 0xcc0) 8 := by
    rw [show sp + 0xcc0 = fr.rsp + 8 by dsimp [sp]; bv_omega]
    exact entry.countRead.of_frame ready.frame
  obtain ⟨b,path,widths,saved,cx,dx,temp,keep⟩ := setupBlock (digits := fr.r9)
    (sp := sp) (congrArg (Value.get 64) rsp) full cr (ready.locals (0xf0,fr.r9) (by simp)) (ready.locals (0x100,1) (by simp))
    (ready.locals (0xcc0,1) (by simp)) (ready.locals (0x1a0,1) (by simp)) ready.widths ready.savedWidths
  have whole : RamWriteFrame m m' writes := by
    have incl (k : BitVec 64) (hk : 456 ≤ k.toNat ∧ k.toNat ≤ 616) :
        InRegions writes (sp + k) 8 := by
      refine ⟨_,List.mem_cons_self ..,?_⟩
      simp only [InRegion,spAdd _ (by omega : k.toNat ≤ 0xcc0),spAdd _ (by decide : (456 : BitVec 64).toNat ≤ 0xcc0)]
      change _ + 456 ≤ _ + k.toNat ∧ _ + k.toNat + 8 ≤ _ + 456 + 168 ∧ _
      omega
    exact ((((RamWriteFrame.refl m writes).memStore _ (incl 0x260 (by decide))).memStore _
      (incl 0x268 (by decide))).memStore _ (incl 0x258 (by decide))).memStore _ (incl 0x1c8 (by decide))
  have out {a : BitVec 64} {n : Nat} (h : a.toNat+n ≤ 2^64)
      (sep : a.toNat+n ≤ sp.toNat+456 ∨ sp.toNat+624 ≤ a.toNat) : Outside writes a n := by
    refine ⟨h, ?_⟩
    intro r hr
    simp only [writes,List.mem_singleton] at hr
    subst r
    simpa only [spAdd _ (by decide : (456 : BitVec 64).toNat ≤ 0xcc0),BitVec.reduceToNat,
      Nat.add_assoc] using sep
  have after {a : BitVec 64} {n : Nat} (h : fr.rsp.toNat - 48 ≤ a.toNat) (hn : a.toNat+n ≤ 2^64) :
      Outside writes a n := out hn (Or.inr (by omega))
  have keepWord (k : BitVec 64) (h : k.toNat ≤ 48) :
      memLoad m' (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply whole.memLoad_eq
    apply after <;> rw [sub _ (by omega)] <;> omega
  have frame : RamWriteFrame fr.original m' (coreWrites fr) := by
    apply ready.frame.trans whole
    intro r hr
    simp only [writes,List.mem_singleton] at hr
    subst r
    refine ⟨fr.region,List.mem_cons_self ..,?_,?_⟩ <;>
      simp only [Activation.region,entry.low,sub 3800 (by decide),spAdd 456 (by decide),BitVec.reduceToNat] <;> omega
  have sameGot (ptr : BitVec 64) (h₁ : 0x203de0 ≤ ptr.toNat) (h₂ : ptr.toNat ≤ 0x203e20) :
      memLoad m' ptr 64 = memLoad m ptr 64 := by
    apply whole.memLoad_eq
    apply out <;> simp only [Nat.reduceDiv] <;> omega
  have first := ready.locals (0x1a0,1) (by simp)
  have table := ready.locals (0x1c0,fr.rcx) (by simp)
  have dest := ready.locals (0x248,fr.rdi) (by simp)
  have locals : ∀ kv ∈ ([(0x1a0,1),(0x1c0,fr.rcx),(0x1c8,0xfffffffffff8),(0x248,fr.rdi),
      (0x258,66),(0x260,66),(0x268,66)] : List (BitVec 64 × BitVec 64)),
      memLoad m' (sp + kv.1) 64 = kv.2 := by
    change memLoad m (sp+0x1a0) 64 = 1 at first
    change memLoad m (sp+0x1c0) 64 = fr.rcx at table
    change memLoad m (sp+0x248) 64 = fr.rdi at dest
    intro kv hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [m',setupMemory] <;>
      refine_norm [first,table,dest]
  have digits {base : BitVec 64} {v : Vector (BitVec 8) 33} (h : fr.rsp.toNat ≤ base.toNat)
      (hb : base.toNat + 33 ≤ 2^32) (words : WordsAt m base 8 v) : WordsAt m' base 8 v := by
    intro i hi
    apply (whole.memLoad_eq _).trans (words i hi)
    apply after
    all_goals simp only [wordAddr,Nat.reduceDiv,Nat.one_mul,BitVec.toNat_add,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega),Nat.mod_eq_of_lt (show base.toNat+i < 2^64 by omega)] <;> omega
  have natTable := entry.tablePtr
  have natDigits := entry.digitPtr
  have tables (k : BitVec 64) (hk : k.toNat ≤ 960) : Outside writes (fr.rcx+k) 960 := by
    rw [natTable,BitVec.add_assoc]
    apply after <;> rw [add _ (by rw [BitVec.toNat_add_of_lt (by change 4008+k.toNat < 2^64; omega)]; change 4008+k.toNat ≤ 6320; omega),
      BitVec.toNat_add_of_lt (by change 4008+k.toNat < 2^64; omega)] <;> simp only [BitVec.reduceToNat] <;> omega
  obtain ⟨p,valid,stored,val⟩ := ready.accumulator
  refine ⟨b,m',path,?_,widths,saved,⟨frame,?_,?_,?_,?_,locals⟩,⟨p,valid,stored.of_frame whole ?_,val⟩,cx,dx,temp⟩
  · change Atom.All _ b m' (Fn11c880.frameAt .l11d7ef fr)
    simp only [Fn11c880.frameAt,Fn11c880.frameAtG2,Atom.All,Atom.Holds]
    refine ⟨(keep 4 (by decide)).trans rsp,(keep 22 (by decide)).trans df,(keep 39 (by decide)).trans mx,
      (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
      (keepWord 48 (by decide)).trans bx,(keepWord 40 (by decide)).trans r12,
      (keepWord 32 (by decide)).trans r13,(keepWord 24 (by decide)).trans r14,
      (keepWord 16 (by decide)).trans r15,(keepWord 8 (by decide)).trans bp,
      retRead.of_frame whole,?_,retLow,stack.of_frame whole,low,align,gRead1.of_frame whole,
      (sameGot 0x203de0 (by decide) (by decide)).trans got1,gRead2.of_frame whole,
      (sameGot 0x203e20 (by decide) (by decide)).trans got2,sep,trivial⟩
    exact (whole.memLoad_eq (after (by omega) (by change fr.rsp.toNat + 8 ≤ 2^64; omega))).trans ret
  · exact ready.firstTable.of_frame whole (by simpa using tables 0 (by decide))
  · exact ready.secondTable.of_frame whole (tables 960 (by decide))
  · refine digits ?_ ?_ ready.firstDigits <;> rw [natDigits,add _ (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
  · refine digits ?_ ?_ ready.secondDigits <;> rw [natDigits,show fr.rsp + 16 + 33 = fr.rsp + 49 by bv_omega,add _ (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
  · apply out <;> rw [sub 2960 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega

end K256.Proofs.Generate.Generator.Multiply
