import K256.Proofs.Signing.Nonce.Initialize.Seed.Stages
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem encodeDispatch {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (ready : ReducedLimbs fr a m x)
    (upper : Writable Extracted.programImage m fr.rsp 784)
    (order : memLoad m (fr.rsp + 16) 64 = fr.rsp + 616) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10126c,a,m⟩ =
      .call ⟨.l100000,b,memStore m (fr.rsp - 288) (0x101295#64)⟩
        ⟨.l101295,#v[],rfl,some ⟨64,0x101295⟩⟩ ∧
      b[4] = ⟨64,fr.rsp - 288⟩ ∧ b[1] = ⟨64,fr.rdx⟩ ∧ b[2] = ⟨64,fr.rsp - 80⟩ ∧
      b[3] = ⟨64,fr.rdx⟩ ∧ b[6] = ⟨64,fr.rsp + 616⟩ ∧ b[7] = ⟨64,fr.rsp - 272⟩ ∧
      b[12] = ⟨64,fr.rsp - 80⟩ ∧ b[15] = ⟨64,fr.rsp + 616⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,8,9,13,14,22,39,50,51] → b[i] = a[i]) := by
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,_,_,_,_,_,_,len,_,_,_,_,_,_,_,_,_,_,_,win,_⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 280 := congrArg (Value.get 64) sp
  have bp : a[5].get 64 = fr.rsp - 272 := congrArg (Value.get 64) ready.source
  refine ⟨?_,?run,?rest⟩
  case run =>
    cfg_eval [rsp,bp]
    simp only [order, len]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10126c)
    rfl
  case rest =>
    refine ⟨rfl,rfl,?_,rfl,rfl,rfl,?_,rfl,?_⟩
    · congr 1 <;> bv_omega
    · congr 1 <;> bv_omega
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

open Standards.SECG.ECC Standards.SECG.DomainParameters
open Generate.Generator.Multiply (scalarWords)

private theorem getWidth (v : Value) (w : v.width = 64) : v = ⟨64,v.get 64⟩ := by
  cases v
  cases w
  rfl

theorem serializeDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {digest : ByteArray}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (secretLen : fr.rdx = 32)
    (orderPtr : memLoad fr.original (fr.rsp + 16) 64 = fr.rsp + 616)
    (orderWords : WordsAt fr.original (fr.rsp + 616) 64 (scalarWords Secp256k1.domain.n))
    (ready : ReducedLimbs fr a m ((Encoding.octetsToNat digest) % Secp256k1.domain.n)) :
    ∃ b n, Verify.Core.Reaches .l10126c a m .l101295 b n ∧ Prepared fr b n digest := by
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,r14,mx,ft,fc,s9,s2,s6,s7,s3,s12,s13,s14,s15,s5,readRet,ret0,retLow,stack,space,
    align,rd0,v0,rd1,v1,rd2,v2,rd3,v3,apart,_⟩ := atoms
  let u := fr.rsp
  change 2208 ≤ u.toNat at depth
  change u.toNat + 784 < 2^32 at limit
  have off (k : BitVec 64) (hk : k.toNat ≤ 2208) : (u-k).toNat = u.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have plus (k : BitVec 64) (hk : k.toNat ≤ 784) : (u+k).toNat = u.toNat+k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
    omega
  have orderLoad (a : BitVec 64) (ha : u.toNat ≤ a.toNat) (hh : a.toNat + 8 ≤ 2^64) :
      memLoad m a 64 = memLoad fr.original a 64 := by
    apply ready.writes.memLoad_eq
    refine ⟨hh, fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change fr.low.toNat + (u.toNat - fr.low.toNat) ≤ a.toNat
    rw [low]
    change (u - 2208).toNat + (u.toNat - (u - 2208).toNat) ≤ _
    rw [show (u-2208).toNat = u.toNat-2208 from off 2208 (by decide)]
    omega
  have upper := window.of_frame ready.writes
  have p16 : (u + 16).toNat = u.toNat + 16 := plus 16 (by decide)
  obtain ⟨b, run, b4,b1,b2,b3,b6,b7,b12,b15,keep⟩ := encodeDispatch ready upper
    ((orderLoad (u+16) (by rw [p16]; omega) (by rw [p16]; omega)).trans orderPtr)
  let n := memStore m (u-288) (0x101295#64)
  let child := {fr with
    original := n, rsp := u-288, low := u-496, ret := 0x101295
    rcx := fr.rdx, rdx := u-80, rbx := fr.rdx, rbp := u-272, rsi := u+616, rdi := u-272
    r8 := a[8].get 64, r9 := a[9].get 64, r12 := u-80, r13 := a[13].get 64, r14 := fr.rdi, r15 := u+616}
  have pushed : RamWriteFrame m n [⟨(u-288).toNat,8⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _,?_⟩
    change (u-288).toNat + 8 ≤ 2^64
    rw [show (u-288).toNat = u.toNat-288 from off 288 (by decide)]
    omega
  have childSp : child.rsp.toNat = u.toNat - 288 := off 288 (by decide)
  have childLow : child.low.toNat = u.toNat - 496 := off 496 (by decide)
  have stack' := stack.of_frame pushed
  have upper' := upper.of_frame pushed
  have stackBase : (fr.rsp - 2208).toNat = u.toNat - 2208 := off 2208 (by decide)
  have cut : child.rsp - 208 = child.low := by change u-288-208 = u-496; bv_omega
  have keepSlot (addr : BitVec 64) (hlo : 0x203dd0 ≤ addr.toNat) (hhi : addr.toNat+8 ≤ 0x203e28) :
      memLoad n addr 64 = memLoad m addr 64 := by
    apply pushed.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change addr.toNat + 8 ≤ (u-288).toNat ∨ (u-288).toNat + 8 ≤ addr.toNat
    change 0x2046c8 ≤ u.toNat ∨ u.toNat ≤ 0x203dd0 at apart
    rw [show (u-288).toNat = u.toNat-288 from off 288 (by decide)]
    omega
  have childEntry : Atom.All Extracted.programImage b n (Fn100000.frameAt .l100000 child) := by
    simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨b4,(keep 22 (by decide)).trans df,b1,b2,b3,(keep 5 (by decide)).trans ready.source,
      b6,b7,(keep 8 (by decide)).trans (getWidth _ (ready.widths 8 (by decide))),
      (keep 9 (by decide)).trans (getWidth _ (ready.widths 9 (by decide))),b12,
      (keep 13 (by decide)).trans (getWidth _ ready.r13Width),(keep 14 (by decide)).trans r14,b15,
      (keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
      stack'.readable.sub (by rw [stackBase, childSp]; omega) (by rw [stackBase, childSp]; omega),
      memLoad_memStore_same _ _ _ (by decide) (by decide),by change (0x101295#64).toNat < 2^32; decide,
      ?_,?_,?_,rd0.of_frame pushed,(keepSlot _ (by decide) (by decide)).trans v0,
      rd1.of_frame pushed,(keepSlot _ (by decide) (by decide)).trans v1,
      rd3.of_frame pushed,(keepSlot _ (by decide) (by decide)).trans v3,?_,trivial⟩
    · rw [cut]; exact stack'.sub (by rw [stackBase,childLow]; omega) (by rw [stackBase,childLow]; omega)
    · rw [childLow,childSp]; omega
    · rw [childSp]; change u.toNat % 16 = 8 at align; omega
    · rw [childSp]; change 0x2046c8 ≤ u.toNat ∨ u.toNat ≤ 0x203dd0 at apart; omega
  have srcNat : child.rdi.toNat = u.toNat - 272 := off 272 (by decide)
  have dstNat : child.rdx.toNat = u.toNat - 80 := off 80 (by decide)
  have orderNat : child.rsi.toNat = u.toNat + 616 := plus 616 (by decide)
  have readS : Readable n child.rdi 32 :=
    stack'.readable.sub (by rw [stackBase,srcNat]; omega) (by rw [stackBase,srcNat]; omega)
  have readO : Readable n child.rsi 32 :=
    upper'.readable.sub (by change u.toNat ≤ _; rw [orderNat]; omega)
      (by change _ ≤ u.toNat+784; rw [orderNat]; omega)
  have writeD : Writable Extracted.programImage n child.rdx 32 :=
    stack'.sub (by rw [stackBase,dstNat]; omega) (by rw [stackBase,dstNat]; omega)
  have wordNat (p : BitVec 64) (hp : p.toNat + 32 ≤ 2^64) (i : Nat) (hi : i < 4) :
      (wordAddr p 64 i).toNat = p.toNat + 8*i := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8*i) (by omega), Nat.mod_eq_of_lt (by omega)]
  have afterPush (p : BitVec 64) (hp : p.toNat + 32 ≤ 2^64) (ha : u.toNat-280 ≤ p.toNat)
      (i : Nat) (hi : i < 4) :
      memLoad n (wordAddr p 64 i) 64 = memLoad m (wordAddr p 64 i) 64 := by
    apply pushed.memLoad_eq
    have wi := wordNat p hp i hi
    refine ⟨by rw [wi]; omega, fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change child.rsp.toNat + 8 ≤ _
    rw [childSp,wi]; omega
  have orderTop : child.rsi.toNat + 32 ≤ 2^64 := by rw [orderNat]; omega
  have ws : WordsAt n child.rdi 64 (scalarWords ((Encoding.octetsToNat digest) % Secp256k1.domain.n)) := by
    intro i hi
    rw [afterPush _ (by rw [srcNat]; omega) (by rw [srcNat]; omega) i hi]
    exact ready.words i hi
  have wo : WordsAt n child.rsi 64 (scalarWords Secp256k1.domain.n) := by
    intro i hi
    rw [afterPush _ orderTop (by rw [orderNat]; omega) i hi,orderLoad _]
    · exact orderWords i hi
    · rw [wordNat _ orderTop i hi,orderNat]; omega
    · rw [wordNat _ orderTop i hi]; omega
  obtain ⟨out,exec,tag,done,widths,written,encoded⟩ :=
    encodeWords childEntry (by rw [childSp]; omega) cut.symm
      (by rw [childSp,srcNat]; omega) (by rw [srcNat,dstNat]; omega)
      (by rw [childSp,orderNat]; omega) secretLen readS readO writeD ws wo
  have route := Verify.Core.Lincomb.reachesCall run exec tag
  let regions : List MemoryRegion := [⟨child.low.toNat,216⟩, ⟨child.rdx.toNat,32⟩]
  have frame : RamWriteFrame m out.store regions := by
    apply ((RamWriteFrame.refl m regions).trans pushed ?_).trans written
    · intro r hr
      rcases List.mem_cons.mp hr with eq | mem
      · subst r
        refine ⟨_,List.mem_cons_self, Nat.le_refl _,?_⟩
        change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ child.low.toNat + 216
        rw [childSp,childLow]; omega
      · obtain rfl := List.mem_singleton.mp mem
        exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_,List.mem_cons_self,?_,?_⟩
      · change child.low.toNat ≤ child.rsp.toNat; rw [childLow,childSp]; omega
      · change child.rsp.toNat + 8 ≤ child.low.toNat + 216; rw [childLow,childSp]; omega
  have total := ready.writes.trans frame (by
    intro r hr
    refine ⟨fr.region,List.mem_singleton_self _,?_⟩
    change fr.low.toNat ≤ r.start ∧ r.start + r.size ≤ fr.low.toNat + (u.toNat-fr.low.toNat)
    rw [low]
    change (u-2208).toNat ≤ _ ∧ _ ≤ (u-2208).toNat + (u.toNat-(u-2208).toNat)
    rcases List.mem_cons.mp hr with eq | mem
    · subst r; change (u-2208).toNat ≤ child.low.toNat ∧ child.low.toNat+216 ≤ _
      rw [childLow,show (u-2208).toNat = u.toNat-2208 from stackBase]; omega
    · obtain rfl := List.mem_singleton.mp mem
      change (u-2208).toNat ≤ child.rdx.toNat ∧ child.rdx.toNat + 32 ≤ _
      rw [dstNat,show (u-2208).toNat = u.toNat-2208 from stackBase]; omega)
  have preserved (p : BitVec 64) (small : p.toNat + 8 ≤ 2^64)
      (left : p.toNat + 8 ≤ u.toNat-496 ∨ u.toNat-280 ≤ p.toNat)
      (right : p.toNat + 8 ≤ u.toNat-80 ∨ u.toNat-48 ≤ p.toNat) :
      memLoad out.store p 64 = memLoad m p 64 := by
    apply frame.memLoad_eq
    refine ⟨small, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with eq | mem
    · subst r
      change _ ≤ child.low.toNat ∨ child.low.toNat+216 ≤ _
      rw [childLow]; omega
    · obtain rfl := List.mem_singleton.mp mem
      change _ ≤ child.rdx.toNat ∨ child.rdx.toNat+32 ≤ _
      rw [dstNat]; omega
  have saved (k : BitVec 64) (hk : k.toNat ≤ 48 ∨ 88 ≤ k.toNat ∧ k.toNat ≤ 112) :
      memLoad out.store (u-k) 64 = memLoad m (u-k) 64 := by
    apply preserved <;> rw [off k (by omega)] <;> omega
  have sameSlot (p : BitVec 64) (lo : 0x203dd0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x203e28) :
      memLoad out.store p 64 = memLoad m p 64 := by
    change 0x2046c8 ≤ u.toNat ∨ u.toNat ≤ 0x203dd0 at apart
    apply preserved <;> omega
  simp only [Fn100000.doneAt,Atom.All,Atom.Holds] at done
  obtain ⟨osp,odf,obx,obp,o12,o13,o14,o15,omx,oft,ofc,_⟩ := done
  have rsp : out.values[4] = ⟨64,fr.rsp-280⟩ := by
    refine osp.trans (congrArg (Value.mk 64) ?_)
    change u-288+8 = u-280
    bv_omega
  have rret := saved 0 (by decide)
  rw [show u - (0 : BitVec 64) = u by bv_omega] at rret
  refine ⟨_,_,route,⟨⟨?_,total⟩,o12,o15,congrArg Value.width obp,congrArg Value.width o13,widths,encoded⟩⟩
  simp only [Fn100ea0.frameAt,Fn100ea0.frameAtG1,Atom.All,Atom.Holds]
  refine ⟨rsp,odf,obx,o14,omx,oft,ofc,(saved 112 (by decide)).trans s9,
    (saved 104 (by decide)).trans s2,(saved 96 (by decide)).trans s6,(saved 88 (by decide)).trans s7,
    (saved 48 (by decide)).trans s3,(saved 40 (by decide)).trans s12,(saved 32 (by decide)).trans s13,
    (saved 24 (by decide)).trans s14,(saved 16 (by decide)).trans s15,(saved 8 (by decide)).trans s5,
    readRet.of_frame frame,rret.trans ret0,retLow,stack.of_frame frame,space,align,rd0.of_frame frame,
    (sameSlot _ (by decide) (by decide)).trans v0,rd2.of_frame frame,(sameSlot _ (by decide) (by decide)).trans v2,?_,trivial⟩
  omega

end K256.Proofs.Signing.Nonce.Initialize
