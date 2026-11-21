import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Call
import K256.Proofs.Common.Encoding
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Verify.Core.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC ParseSignature
open Generate.Generator.Multiply (scalarWords)

private theorem octetsToNat_natToOctets (n x : Nat) (bound : x < 256 ^ n) :
    Encoding.octetsToNat (Encoding.natToOctets n x) = x := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simp only [Nat.pow_zero] at bound; omega
    subst x
    decide +kernel
  | succ n ih =>
    rw [Common.Encoding.natToOctets_succ]
    have small : x / 256 < 256 ^ n := by rw [Nat.pow_succ] at bound; omega
    rw [Encoding.octetsToNat, ByteArray.data_append, Array.foldl_append]
    change 256 * Encoding.octetsToNat (Encoding.natToOctets n (x / 256)) +
      (UInt8.ofNat (x % 256)).toNat = x
    rw [ih _ small, UInt8.toNat_ofNat', Nat.mod_mod]
    omega

theorem scalarValue_of_octets {m : Ram} {src : BitVec 64} {x : Nat}
    (encoded : (⟨src.toNat, 32⟩ : MemoryRegion).HasBytes m (Encoding.natToOctets 32 x))
    (bound : x < 2^256) : ParseSignature.scalarValue m src = x := by
  have eq := Common.octetsToNat_extract_eq_words encoded
    (off := 0) (by rw [Common.Encoding.natToOctets_size]; decide)
  have whole : (Encoding.natToOctets 32 x).extract 0 (0 + 32) = Encoding.natToOctets 32 x := by
    calc
      _ = (Encoding.natToOctets 32 x).extract 0 (Encoding.natToOctets 32 x).size :=
        congrArg ((Encoding.natToOctets 32 x).extract 0) (Common.Encoding.natToOctets_size 32 x).symm
      _ = _ := ByteArray.extract_zero_size
  rw [whole, octetsToNat_natToOctets _ _ (by
    rwa [show 256^32 = 2^256 by decide +kernel])] at eq
  simpa only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, ParseSignature.scalarValue] using eq.symm


private abbrev fillRet : BitVec 64 := 0x105306

private def setupRegion (fr : Activation) : MemoryRegion := ⟨(fr.rsp - 496).toNat, 176⟩

private theorem fillSetup {fr : Activation} {a : Registers} {m : Ram}
    (sp : a[4].get 64 = localSp fr) (src : a[15].get 64 = localSp fr + 320)
    (window : Writable Extracted.programImage m (fr.rsp - 496) 176) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l105292,a,m⟩ =
      .call ⟨.l127d70,b,n⟩ ⟨.l105306,#v[],rfl,some ⟨64,fillRet⟩⟩ ∧
      b[4] = ⟨64,fr.rsp - 496⟩ ∧ b[6] = ⟨64,32⟩ ∧ b[7] = ⟨64,localSp fr + 320⟩ ∧
      b[1] = ⟨64,4⟩ ∧ b[2] = ⟨64,localSp fr + 136⟩ ∧ b[8] = ⟨64,256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n [setupRegion fr] ∧ memLoad n (fr.rsp - 496) 64 = fillRet := by
  have stack : Writable Extracted.programImage m (localSp fr - 8) 176 := by
    rw [show localSp fr - 8 = fr.rsp - 496 by unfold localSp; bv_omega]
    exact window
  refine ⟨?args, ?mem, ?run, ?post⟩
  case run =>
    cfg_eval [sp, src]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => coreText x (code_l105292 x hx)))
    rw [show localSp fr - 8 = fr.rsp - 496 by unfold localSp; bv_omega]
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have := window.readable.low
      unfold setupRegion
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

private def child (fr : Activation) (b : Registers) (n : Ram) : Activation :=
  { fr with
    original := n, rsp := fr.rsp - 496, low := fr.rsp - 704, ret := fillRet
    rbx := fr.rdi, rsi := 32, rdi := localSp fr + 320, rdx := localSp fr + 136
    rcx := 4, r8 := 256, r9 := b[9].get 64
    r12 := b[12].get 64, r13 := b[13].get 64, r14 := b[14].get 64, r15 := localSp fr + 320 }

private theorem eqWidth (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  cases v
  cases h
  rfl

theorem phaseFrame {fr : Activation} {a b c : Registers} {p : Curve.Point}
    {digest : ByteArray} {r s : Nat} {m n : Ram} {regions : List MemoryRegion}
    (e : Entry fr a p digest r s) (h : Phase fr b m)
    (sp : c[4] = ⟨64, localSp fr⟩) (bx : c[3] = ⟨64, fr.rdi⟩) (bp : c[5] = ⟨64, fr.rbp⟩)
    (df : c[22] = ⟨1,0⟩) (mx : c[39] = ⟨32,fr.mxcsr⟩)
    (ft : c[50] = ⟨16,fr.ftw⟩) (fc : c[51] = ⟨16,fr.fcw⟩)
    (frame : RamWriteFrame m n regions)
    (within : ∀ reg ∈ regions, fr.low.toNat ≤ reg.start ∧ reg.start + reg.size ≤ fr.rsp.toNat - 40) :
    Phase fr c n := by
  have room := e.stackRoom
  have lo := e.low
  have saved (d : Nat) (hd : d ≤ 40) :
      memLoad n (fr.rsp - BitVec.ofNat 64 d) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 := by
    have addr := coreSub e (show d ≤ 12456 by omega)
    apply frame.memLoad_eq
    refine ⟨by omega, fun reg hr => Or.inr ?_⟩
    have := (within reg hr).2
    omega
  refine ⟨⟨sp,bx,bp,df,mx,ft,fc,(saved 40 (by decide)).trans h.rbx,(saved 32 (by decide)).trans h.r12,
    (saved 24 (by decide)).trans h.r13,(saved 16 (by decide)).trans h.r14,(saved 8 (by decide)).trans h.r15⟩,
    h.frame.trans frame ?_⟩
  intro reg hr
  have w := within reg hr
  refine ⟨fr.region,List.mem_singleton_self _,w.1,?_⟩
  change _ ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
  omega

theorem fillX {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray} {r s x : Nat}
    {m : Ram} (e : Entry fr a p digest r s) (h : Phase fr b m)
    (ptr : b[15] = ⟨64, localSp fr + 320⟩) (w9 : b[9].width = 64) (w12 : b[12].width = 64)
    (w13 : b[13].width = 64) (w14 : b[14].width = 64)
    (value : scalarValue m (localSp fr + 320) = x)
    (hr : WordsAt m (localSp fr + 256) 64 (scalarWords r)) :
    ∃ c n, Reaches .l105292 b m .l10530e c n ∧ Phase fr c n ∧
      c[15] = ⟨64, localSp fr + 320⟩ ∧ c[12].width = 64 ∧ c[13].width = 64 ∧
      ArgumentWidths c ∧ WordsAt n (localSp fr + 136) 64 (scalarWords x) ∧
      WordsAt n (localSp fr + 256) 64 (scalarWords r) := by
  have room := e.stackRoom
  have upper := e.low
  have low := e.low_toNat
  have offset (d : Nat) (hd : d ≤ 12456) := coreSub e hd
  have shift (off : BitVec 64) : (localSp fr + off).toNat =
      (fr.rsp - (488 - off)).toNat := by
    rw [show localSp fr + off = fr.rsp - (488 - off) by unfold localSp; bv_omega]
  have s496 : (fr.rsp - 496).toNat = fr.rsp.toNat - 496 := offset 496 (by decide)
  have n320 : (localSp fr + 320).toNat = fr.rsp.toNat - 168 := (shift 320).trans (offset 168 (by decide))
  have n136 : (localSp fr + 136).toNat = fr.rsp.toNat - 352 := (shift 136).trans (offset 352 (by decide))
  have n256 : (localSp fr + 256).toNat = fr.rsp.toNat - 232 := (shift 256).trans (offset 232 (by decide))
  have window := coreWindow e h.frame (d := 496) (len := 176) (by decide) (by decide)
  obtain ⟨args,n,push,sp,si,di,cx,dx,r8,keep,written,ret⟩ :=
    fillSetup (congrArg (Value.get 64) h.sp) (congrArg (Value.get 64) ptr) window
  let ch := child fr args n
  have chTop : ch.rsp.toNat = fr.rsp.toNat - 496 := s496
  have chLow : ch.low.toNat = fr.rsp.toNat - 704 := offset 704 (by decide)
  have chInput : ch.rdi.toNat = fr.rsp.toNat - 168 := n320
  have chOutput : ch.rdx.toNat = fr.rsp.toNat - 352 := n136
  have setupFrame := h.frame.trans written (by
    intro reg hm
    obtain rfl := List.mem_singleton.mp hm
    refine ⟨fr.region,List.mem_singleton_self _,?_⟩
    change fr.low.toNat ≤ (fr.rsp - 496).toNat ∧ (fr.rsp - 496).toNat + 176 ≤
      fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    omega)
  have alignAtoms := e.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at alignAtoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,align,
    _,_,_,_,_,_,gotApart,_⟩ := alignAtoms
  have got := Fn127d70.callSlots_loaded (sections := Extracted.programSections)
    (by simp [Verify.LIR.rodataSection, Extracted.programSections]) (e.loaded_of_frame setupFrame)
  obtain ⟨got0r,got0v⟩ := got (0x203dd0,0x12a820) (by decide)
  obtain ⟨got1r,got1v⟩ := got (0x203de0,0x129770) (by decide)
  obtain ⟨got2r,got2v⟩ := got (0x203e20,0x100a20) (by decide)
  have shWin : Writable Extracted.programImage n (ch.rsp - 208) 208 := by
    rw [show ch.rsp - 208 = fr.rsp - BitVec.ofNat 64 704 by change fr.rsp - 496 - 208 = _; bv_omega]
    exact coreWindow e setupFrame (by decide) (by decide)
  have src : Readable n ch.rdi 32 := by
    rw [show ch.rdi = fr.rsp - BitVec.ofNat 64 168 by change fr.rsp - 488 + 320 = _; bv_omega]
    exact (coreWindow e setupFrame (by decide : 168 ≤ 12456) (by decide)).readable
  have dst : Writable Extracted.programImage n ch.rdx 32 := by
    rw [show ch.rdx = fr.rsp - BitVec.ofNat 64 352 by change fr.rsp - 488 + 136 = _; bv_omega]
    exact coreWindow e setupFrame (by decide) (by decide)
  have retRead : Readable n ch.rsp 8 := (coreWindow e setupFrame (by decide : 496 ≤ 12456) (by decide)).readable
  change fr.rsp.toNat % 16 = 8 at align
  change 0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at gotApart
  have entry : Atom.All Extracted.programImage args n (Fn127d70.frameAt .l127d70 ch) := by
    exact ⟨sp,(keep 22 (by decide)).trans h.df,cx,dx,(keep 3 (by decide)).trans h.dst,
      (keep 5 (by decide)).trans h.rbp,si,di,r8,eqWidth _ ((congrArg Value.width (keep 9 (by decide))).trans w9),
      eqWidth _ ((congrArg Value.width (keep 12 (by decide))).trans w12),
      eqWidth _ ((congrArg Value.width (keep 13 (by decide))).trans w13),
      eqWidth _ ((congrArg Value.width (keep 14 (by decide))).trans w14),
      (keep 15 (by decide)).trans ptr,(keep 39 (by decide)).trans h.mxcsr,
      (keep 50 (by decide)).trans h.ftw,(keep 51 (by decide)).trans h.fcw,
      retRead,ret,by change (0x105306 : Nat) < 2^32; decide,shWin,
      by change ch.low.toNat + 208 ≤ ch.rsp.toNat; omega,
      by change ch.rsp.toNat % 16 = 8; omega,
      got0r,got0v,got1r,got1v,got2r,got2v,
      by change 0x203ef8 ≤ ch.rsp.toNat ∨ ch.rsp.toNat ≤ 0x203dd0; omega,trivial⟩
  have above {addr : BitVec 64} (ha : fr.rsp.toNat - 352 ≤ addr.toNat) (hi : addr.toNat + 32 ≤ 2^64) :
      Outside [callStack ch] addr 32 := by
    refine ⟨hi, fun reg hm => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hm
    change ch.low.toNat + (ch.rsp.toNat + 8 - ch.low.toNat) ≤ addr.toNat
    omega
  have disj : Outside [buffer ch.rdx 32] ch.rdi 32 := by
    refine ⟨by omega, fun reg hm => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hm
    change ch.rdx.toNat + 32 ≤ ch.rdi.toNat
    omega
  have away : Outside [buffer ch.rdx 32] (0x203dd0 : BitVec 64) 8 := by
    refine ⟨by decide, fun reg hm => ?_⟩
    obtain rfl := List.mem_singleton.mp hm
    change (0x203dd0 : Nat) + 8 ≤ ch.rdx.toNat ∨ ch.rdx.toNat + 32 ≤ 0x203dd0
    omega
  obtain ⟨out,run,tag,done_,went,widths,al,limbs⟩ := fillScalar entry rfl rfl rfl src dst
    (above (by omega) (by omega)) (above (by omega) (by omega)) disj away
  have path := resumeCoreCall push run tag
  obtain ⟨retSP,retDF,retBX,retBP,ret12,ret13,_,ret15,retMX,retFT,retFC,_⟩ := done_
  have good : (fr.rsp - 496 + 8 : BitVec 64) = localSp fr := by unfold localSp; bv_omega
  change out.values[4] = ⟨64,fr.rsp - 496 + 8⟩ at retSP
  rw [good] at retSP
  let regions : List MemoryRegion := [⟨ch.low.toNat, 384⟩]
  have regionBounds (reg : MemoryRegion) (hm : reg ∈ regions) :
      fr.low.toNat ≤ reg.start ∧ reg.start + reg.size ≤ fr.rsp.toNat - 40 := by
    obtain rfl := List.mem_singleton.mp hm
    change fr.low.toNat ≤ ch.low.toNat ∧ ch.low.toNat + 384 ≤ _
    omega
  have stageFrame : RamWriteFrame m n regions := (RamWriteFrame.refl m regions).trans written (by
    intro reg hm
    obtain rfl := List.mem_singleton.mp hm
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change ch.low.toNat ≤ (fr.rsp - 496).toNat ∧ (fr.rsp - 496).toNat + 176 ≤ ch.low.toNat + 384
    omega)
  have delta := stageFrame.trans went (by
    intro reg hm
    refine ⟨_,List.mem_singleton_self _,?_⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · change ch.low.toNat ≤ ch.low.toNat ∧ ch.low.toNat + (ch.rsp.toNat - ch.low.toNat) ≤ ch.low.toNat + 384
      omega
    · obtain rfl := List.mem_singleton.mp hm
      change ch.low.toNat ≤ ch.rdx.toNat ∧ ch.rdx.toNat + 32 ≤ ch.low.toNat + 384
      omega)
  have phase := phaseFrame e h retSP retBX retBP retDF retMX retFT retFC delta regionBounds
  have preserved : WordsAt out.store (localSp fr + 256) 64 (scalarWords r) :=
    hr.of_frame delta (by decide) ⟨by omega, fun reg hm => Or.inr (by
      obtain rfl := List.mem_singleton.mp hm
      change ch.low.toNat + 384 ≤ _
      omega)⟩
  have srcSame : scalarValue n ch.rdi = scalarValue m ch.rdi := by
    dsimp only [scalarValue]
    have word (i : Nat) (hi : i < 4) : Common.scalarWord n ch.rdi i = Common.scalarWord m ch.rdi i := by
      unfold Common.scalarWord
      apply congrArg bswapSpec
      apply written.memLoad_eq
      have addr : (ch.rdi + BitVec.ofNat 64 (8 * (3 - i))).toNat =
          ch.rdi.toNat + 8 * (3 - i) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (a := 8 * (3 - i)) (by omega), Nat.mod_eq_of_lt (by omega)]
      refine ⟨by omega, fun reg hm => Or.inr ?_⟩
      obtain rfl := List.mem_singleton.mp hm
      change (fr.rsp - 496).toNat + 176 ≤ _
      omega
    rw [word 3 (by decide), word 2 (by decide), word 1 (by decide), word 0 (by decide)]
  change WordsAt out.store (localSp fr + 136) 64 (scalarWords (scalarValue n ch.rdi)) at limbs
  rw [srcSame, (show scalarValue m ch.rdi = x from value)] at limbs
  have branch : ∃ next, Reaches .l105306 out.values out.store .l10530e next out.store ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,15,22,39,50,51] →
        next[i] = out.values[i]) := by
    have al' : (out.values[0].get 64).setWidth 8 = 255 := by
      simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using al
    refine ⟨?next, .single ?step, ?keep⟩
    case step =>
      change program.step _ _ = _
      unfold Program.step
      cfg_eval [al']
      rfl
    case keep =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨next,br,eq⟩ := branch
  refine ⟨next,out.store,path.trans br,?_,(eq 15 (by decide)).trans ret15,
    congrArg Value.width ((eq 12 (by decide)).trans ret12),
    congrArg Value.width ((eq 13 (by decide)).trans ret13),?_,limbs,preserved⟩
  · exact ⟨⟨(eq 4 (by decide)).trans phase.sp,(eq 3 (by decide)).trans phase.dst,
      (eq 5 (by decide)).trans phase.rbp,(eq 22 (by decide)).trans phase.df,
      (eq 39 (by decide)).trans phase.mxcsr,(eq 50 (by decide)).trans phase.ftw,
      (eq 51 (by decide)).trans phase.fcw,phase.rbx,phase.r12,phase.r13,phase.r14,phase.r15⟩,phase.frame⟩
  · intro i hi
    exact (congrArg Value.width (eq i (by
      simp only [Activation.argumentNumbers, List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega))).trans (widths i hi)

end K256.Proofs.Verify.Core.Affine
