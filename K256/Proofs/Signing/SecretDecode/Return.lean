import K256.Proofs.Signing.SecretDecode.State
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.Affine.Call

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

private def putLimbs (fr : Activation) (m : Ram) : Ram :=
  let m := memStore m (fr.rdi + 8) (word fr 0)
  let m := memStore m (fr.rdi + 16) (word fr 1)
  let m := memStore m (fr.rdi + 24) (word fr 2)
  memStore m (fr.rdi + 32) (word fr 3)

private abbrev resultMem (fr : Activation) (m : Ram) :=
  memStore (putLimbs fr m) fr.rdi (0 : BitVec 64)

private theorem storeLimbs {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (bx : a[3] = ⟨64, fr.rdi⟩)
    (area : Writable Extracted.programImage m fr.rdi 40) (limbs : Limbs fr a) :
    ∃ b, Verify.Core.Reaches .l106f49 a m .l106f5b b (putLimbs fr m) ∧
      b[5].get 64 = 0 ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,6,7,8,9,22,39,50,51] → b[i] = a[i] := by
  obtain ⟨w0,w1,w2,w3,_⟩ := limbs
  have g0 : a[3].get 64 = fr.rdi := congrArg (Value.get 64) bx
  have g1 : a[14].get 64 = word fr 0 := congrArg (Value.get 64) w0
  have g2 : a[15].get 64 = word fr 1 := congrArg (Value.get 64) w1
  have g3 : a[12].get 64 = word fr 2 := congrArg (Value.get 64) w2
  have g4 : a[13].get 64 = word fr 3 := congrArg (Value.get 64) w3
  refine ⟨?_, Semantics.Reaches.single ?step, ?zero, ?keep⟩
  case step =>
    change program.step _ _ = _
    unfold Program.step
    cfg_eval
    simp only [g0,g1,g2,g3,g4]
    simp (disch := slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l106f49 x hx))) only [ite_eq_left]
    rfl
  case zero => rfl
  case keep =>
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem resultPost {fr : Activation} {m : Ram}
    (wf : RamWriteFrame fr.original m [fr.region])
    (wr : Writable Extracted.programImage fr.original fr.rdi 40) :
    RamWriteFrame fr.original (resultMem fr m) [fr.region, ⟨fr.rdi.toNat, 40⟩] ∧
    memLoad (resultMem fr m) fr.rdi 64 = 0 ∧
    WordsAt (resultMem fr m) (fr.rdi + 8) 64 (Vector.ofFn fun i : Fin 4 => word fr i.val) := by
  let regions : List MemoryRegion := [fr.region, ⟨fr.rdi.toNat,40⟩]
  have frame := (RamWriteFrame.refl fr.original regions).trans wf (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have bound := wr.readable.low
  have inside (n : Nat) (hn : n + 8 ≤ 40) : InRegions regions (fr.rdi + BitVec.ofNat 64 n) 8 := by
    have addr : (fr.rdi + BitVec.ofNat 64 n).toNat = fr.rdi.toNat + n := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    exact ⟨_, .tail _ (.head _), by change fr.rdi.toNat ≤ _; omega,
      by change _ ≤ fr.rdi.toNat + 40; omega, by omega⟩
  refine ⟨?_, memLoad_memStore_same _ _ _ (by decide) (by decide), ?_⟩
  · exact ((((frame.memStore _ (inside 8 (by decide))).memStore _ (inside 16 (by decide))).memStore _
      (inside 24 (by decide))).memStore _ (inside 32 (by decide))).memStore _ (by simpa using inside 0 (by decide))
  · intro i hi
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
    all_goals
      simp (disch := store_disch) only [resultMem, putLimbs, Vector.getElem_ofFn, wordAddr,
        Nat.reduceDiv, Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero, memLoad_memStore_same, memLoad_memStore_of_rangeApart] <;>
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)

private theorem resultSlot (fr : Activation) (m : Ram) (dst : fr.rdi = fr.rsp + 40)
    (off : Nat) (slot : off ∈ [0,8,16,24,32,40,48]) :
    memLoad (resultMem fr m) (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at slot
  rcases slot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := store_disch) only [resultMem, putLimbs, dst, BitVec.add_assoc, BitVec.reduceAdd,
      memLoad_memStore_of_rangeApart]

set_option maxHeartbeats 450000 in
theorem returnPath {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (dst : fr.rdi = fr.rsp + 40)
    (writable : Writable Extracted.programImage fr.original fr.rdi 40)
    (h : Frame .l106f49 fr a m) (limbs : Limbs fr a) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106f49, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn106dd0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 40⟩] ∧
      memLoad out.store fr.rdi 64 = 0 ∧
      WordsAt out.store (fr.rdi + 8) 64
        (Vector.ofFn fun i : Fin 4 => word fr i.val) := by
  have atoms := h.atoms
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,bx,mx,ft,fc,bxM,r12M,r13M,r14M,r15M,bpM,retR,retM,retL,area,space,_⟩ := atoms
  obtain ⟨b,reach,zero,keep⟩ := storeLimbs bx (writable.of_frame h.writes) limbs
  have ptr : b[3].get 64 = fr.rdi := congrArg (Value.get 64) ((keep 3 (by decide)).trans bx)
  have stack : b[4].get 64 = fr.rsp - 120 := congrArg (Value.get 64) ((keep 4 (by decide)).trans sp)
  obtain ⟨writes,tag,words⟩ := resultPost h.writes writable
  have win : Writable Extracted.programImage (resultMem fr m) (fr.rsp - 336) 336 := (((((area.memStore _ _).memStore _ _).memStore _ _).memStore _ _).memStore _ _)
  have rd : Readable (resultMem fr m) fr.rsp 8 := (((((retR.memStore _ _).memStore _ _).memStore _ _).memStore _ _).memStore _ _)
  have wr := writable.of_frame h.writes
  have wr4 : Writable Extracted.programImage (putLimbs fr m) fr.rdi 40 := ((((wr.memStore _ _).memStore _ _).memStore _ _).memStore _ _)
  have slot := resultSlot fr m dst
  have saved0 : memLoad (resultMem fr m) fr.rsp 64 = fr.ret := by
    have z := slot 0 (by decide)
    rw [show fr.rsp - BitVec.ofNat 64 0 = fr.rsp from BitVec.sub_zero _] at z
    exact z.trans retM
  have saved48 : memLoad (resultMem fr m) (fr.rsp - 48) 64 = fr.rbx := (slot 48 (by decide)).trans bxM
  have saved40 : memLoad (resultMem fr m) (fr.rsp - 40) 64 = fr.r12 := (slot 40 (by decide)).trans r12M
  have saved32 : memLoad (resultMem fr m) (fr.rsp - 32) 64 = fr.r13 := (slot 32 (by decide)).trans r13M
  have saved24 : memLoad (resultMem fr m) (fr.rsp - 24) 64 = fr.r14 := (slot 24 (by decide)).trans r14M
  have saved16 : memLoad (resultMem fr m) (fr.rsp - 16) 64 = fr.r15 := (slot 16 (by decide)).trans r15M
  have saved8 : memLoad (resultMem fr m) (fr.rsp - 8) 64 = fr.rbp := (slot 8 (by decide)).trans bpM
  have finish : ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106f5b,b,putLimbs fr m⟩,[]⟩ out ∧
      out.store = resultMem fr m ∧ out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn106dd0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values := by
    refine ⟨?_, .done ?run, ?mem, ?tag, ?atoms, ?widths⟩
    case run =>
      unfold Program.step
      cfg_eval
      simp only [ptr,stack,zero,Lift.reduceAddOffset,BitVec.sub_add_cancel,
        saved48,saved40,saved32,saved24,saved16,saved8,saved0,retL,and_true]
      have writeOk : StoreOk Extracted.programImage (putLimbs fr m) fr.rdi 8 0x106f5b 3 := by
        slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l106f5b x hx))
      have readOk : LoadOk (resultMem fr m) fr.rsp 8 := ⟨rd.low,rd.present⟩
      have offset (k : Nat) (hk : k ≤ 336) :
          (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
        have small : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [small]; omega)),small]
      have floor : (fr.rsp - 336).toNat = fr.rsp.toNat - 336 := offset 336 (by decide)
      have pop (k : Nat) (hk : k ≤ 48) (lo : 8 ≤ k) :
          LoadOk (resultMem fr m) (fr.rsp - BitVec.ofNat 64 k) 8 := by
        apply LoadOk.of_region win.readable
        · rw [offset k (by omega), floor]; omega
        · rw [offset k (by omega), floor]; omega
      have p48 : LoadOk (resultMem fr m) (fr.rsp - 48) 8 := pop 48 (by decide) (by decide)
      have p40 : LoadOk (resultMem fr m) (fr.rsp - 40) 8 := pop 40 (by decide) (by decide)
      have p32 : LoadOk (resultMem fr m) (fr.rsp - 32) 8 := pop 32 (by decide) (by decide)
      have p24 : LoadOk (resultMem fr m) (fr.rsp - 24) 8 := pop 24 (by decide) (by decide)
      have p16 : LoadOk (resultMem fr m) (fr.rsp - 16) 8 := pop 16 (by decide) (by decide)
      have p8 : LoadOk (resultMem fr m) (fr.rsp - 8) 8 := pop 8 (by decide) (by decide)
      simp only [ite_eq_left writeOk, ite_eq_left readOk, ite_eq_left p48, ite_eq_left p40,
        ite_eq_left p32, ite_eq_left p24, ite_eq_left p16, ite_eq_left p8]
      rfl
    case mem => rfl
    case tag => rfl
    case atoms =>
      exact ⟨rfl,(keep 22 (by decide)).trans df,rfl,rfl,rfl,rfl,rfl,rfl,
        (keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,trivial⟩
    case widths =>
      rintro ⟨i,hi⟩ member
      have w := h.widths ⟨i,hi⟩ member
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (congrArg Value.width (keep _ (by simp))).trans w
  obtain ⟨out,run,mem,ret,done_,widths⟩ := finish
  exact ⟨out, Program.Exec.of_sem (reach.exec run.sem), ret, done_, widths, mem ▸ writes, mem ▸ tag, mem ▸ words⟩

end K256.Proofs.Signing.SecretDecode
