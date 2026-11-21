import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.TailMemory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

structure TailAccess (fr : Activation) (second : Bool) (m : Ram) : Prop where
  used : Writable Extracted.programImage m (context fr second + 127) 1
  push : Writable Extracted.programImage (marked fr second m) (sp fr - 8) 8
  written : RamWriteFrame fr.original (marked fr second m) [fr.region,⟨fr.rdi.toNat,64⟩]
  gotRead : LoadOk (marked fr second m) 0x203dd0 8
  got : memLoad (marked fr second m) 0x203dd0 64 = 0x12a820
  source : Readable (marked fr second m) (fr.rsp + 351) 1
  stopRead : ∀ ret, LoadOk (tailMemory fr second m ret) (sp fr + 8) 8

theorem tailAccess {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr (.seeded secret reduced))
    (live : Live (tailAt second) fr a m state) : TailAccess fr second m := by
  have dep := env.depth
  have lim := env.limit
  have base := spNat env
  let p := context fr second + 127
  have pn : p.toNat = (sp fr).toNat + (if second then 455 else 287) := by
    cases second <;> simpa only [p, context, Bool.false_eq_true,Bool.true_eq,ite_true,ite_false,
      BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using
        spAddNat env _ (by decide)
  have pn' : p.toNat+1 ≤ fr.rsp.toNat - 48 := by cases second <;> simp_all <;> omega
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have start : fr.low.toNat ≤ p.toNat := by cases second <;> simp_all <;> omega
  have slot : (sp fr-8).toNat = (sp fr).toNat-8 := BitVec.toNat_sub_of_le
    (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have place : InRegions [fr.region,⟨fr.rdi.toNat,64⟩] p 1 := by
    refine ⟨_,List.mem_cons_self,start,?_,by omega⟩
    change p.toNat+1 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat)
    omega
  have localW : RamWriteFrame m (marked fr second m) [⟨p.toNat,1⟩] := by
    have x : InRegions [⟨p.toNat,1⟩] p 1 :=
      ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _,by omega⟩
    exact ((RamWriteFrame.refl m _).memStore (0 : BitVec 8) x).memStore (1 : BitVec 8) x
  have markedW := (live.writes.memStore (0 : BitVec 8) place).memStore (1 : BitVec 8) place
  have tail : FrameTail fr a m := by
    cases second
    · exact live.atoms.2.2.2.2.2.2.2
    · exact live.atoms.2.2.2.2.2
  have tail' : FrameTail fr a (marked fr second m) := frameTailAfter env tail localW (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨start,pn'⟩)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,r,g,_⟩ := tail'
  obtain ⟨_,_,_,high,_,_,_,_,_,_,_,s,_⟩ := env.slicesAt markedW
  change fr.rsp.toNat + 352 < 2^32 at high
  have len : secret.size = 32 := s.1
  have off (k : BitVec 64) (hk : k.toNat ≤ 351) :
      (fr.rsp+k).toNat = fr.rsp.toNat + k.toNat := by rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have big : (fr.rsp+320).toNat = fr.rsp.toNat + 320 := off _ (by decide)
  have endN : (fr.rsp+351).toNat = fr.rsp.toNat + 351 := off _ (by decide)
  have src := Readable.of_hasBytes s (by change (fr.rsp+320).toNat +32 < 2^32; omega)
  change Readable (marked fr second m) (BitVec.ofNat 64 (fr.rsp+320).toNat) secret.size at src
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,len] at src
  have stopN : (sp fr+8).toNat = (sp fr).toNat + 8 := spAddNat env 8 (by decide)
  have stopRead : Readable m (sp fr+8) 8 :=
    (stackWritable env live.writes (by omega) (by omega)).readable
  refine ⟨stackWritable (p := p) env live.writes start (by omega), stackWritable env markedW (by omega) (by omega),
    markedW, LoadOk.of_region r (Nat.le_refl _) (Nat.le_refl _), g, src.sub (by omega) (by omega), ?_⟩
  intro ret
  have x := (((stopRead.memStore p (0 : BitVec 8)).memStore p (1 : BitVec 8)).memStore (sp fr-8) ret).memStore
    (context fr second+64) (memLoad (memStore (marked fr second m) (sp fr-8) ret) (fr.rsp+351) (8*1))
  exact LoadOk.of_region x (Nat.le_refl _) (Nat.le_refl _)

theorem loopLive {fr : Activation} {state : State} {input : Input}
    {a b : Verify.Core.Registers} {m n : Ram} {rs : List MemoryRegion} (second : Bool)
    (env : Environment fr input) (live : Live (tailAt second) fr a m state) (slots : Slots fr n)
    (writes : RamWriteFrame m n rs) (locality : LocalWrites fr rs)
    (same : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i])
    (r14 : second = false → b[14] = a[14])
    (widths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64) :
    Live (loopAt second) fr b n state := by
  apply liveAfter env live writes locality _ widths (by cases second <;> intro h <;> cases h)
  cases second
  · obtain ⟨rsp,df,h14,mx,ft,fc,_,tail⟩ := live.atoms
    have saved : memLoad n (fr.rsp-0x250) 64 = fr.rdi := by
      rw [show fr.rsp-0x250 = sp fr+120 by bv_omega]
      exact slots.state
    exact ⟨(same 4 (by decide)).trans rsp, (same 22 (by decide)).trans df,
      (r14 rfl).trans h14, (same 39 (by decide)).trans mx, (same 50 (by decide)).trans ft,
      (same 51 (by decide)).trans fc,saved,frameTailAfter (b := b) env (show FrameTail fr a m from tail) writes locality⟩
  · obtain ⟨rsp,df,mx,ft,fc,tail⟩ := live.atoms
    exact ⟨(same 4 (by decide)).trans rsp, (same 22 (by decide)).trans df,
      (same 39 (by decide)).trans mx, (same 50 (by decide)).trans ft, (same 51 (by decide)).trans fc,
      frameTailAfter (b := b) env (show FrameTail fr a m from tail) writes locality⟩

def copyAt (second : Bool) : Label := if second then .l104872 else .l1042c0
def advanceAt (second : Bool) : Label := if second then .l10489d else .l1042e3
def tailRet (second : Bool) : BitVec 64 := if second then 0x10489d else 0x1042e3

structure AtCopy (second : Bool) (fr : Activation) (a c : Verify.Core.Registers) : Prop
    extends Cursor second fr c 0 where
  rsp : c[4].get 64 = sp fr - 8
  di : c[7].get 64 = context fr second + 64
  si : c[6].get 64 = fr.rsp + 351
  dx : c[2].get 64 = 1
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = a[i]
  r14 : second = false → c[14] = a[14]
  widths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → c[i].width = 64

def PrepareCopy (second : Bool) : Prop :=
  ∀ {fr : Activation} {a : Verify.Core.Registers} {m : Ram},
    a[4] = ⟨64, sp fr⟩ → Pending second fr a →
    (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64) →
    TailAccess fr second m →
    ∃ b c, Verify.Core.Reaches (tailAt second) a m (copyAt second) b (cleared fr second m) ∧
      program.runBlock (dialect Extracted.programImage) ⟨copyAt second,b,cleared fr second m⟩ =
        .call ⟨.l12a820,c,memStore (marked fr second m) (sp fr-8) (tailRet second)⟩
          (Verify.Core.Lincomb.callResume (advanceAt second) (tailRet second)) ∧ AtCopy second fr a c

def Advance (second : Bool) : Prop :=
  ∀ {fr : Activation} {a : Verify.Core.Registers} {m : Ram}, a[4] = ⟨64, sp fr⟩ →
    Cursor second fr a 0 → LoadOk m (sp fr+8) 8 → memLoad m (sp fr+8) 64 = fr.rsi+48 →
    (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64) →
    ∃ b, Verify.Core.Reaches (advanceAt second) a m (loopAt second) b m ∧
      Cursor second fr b 16 ∧ (∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) ∧
      (second = false → b[14] = a[14]) ∧
      (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64)

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
