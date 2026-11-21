import K256.Proofs.Ecdh.Multiply.Bases.Frame
import K256.Proofs.Ecdh.Multiply.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Negate.Machine
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.ScalarNeg

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Negate (storeFour selectFour selectedMemory dispatchMemory Dispatched selectPrefix dispatchTail)
open Split.Caller (slot peerSlotNat peerSpNat peerPushNat peerStackAccess peerSlotWrite peerStackBelowWrite)

private def spans : Spans := [(0x48,1),(0x128,32),(0x1d0,32),(0x270,32),(0x418,32)]

private abbrev KeepSystem (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]

private structure Pushed (l resume : Label) (fr : Activation) (a b : Registers) (m n : Ram)
    (ret : BitVec 64) (dst : Nat) (x : Vector (BitVec 64) 4) : Prop where
  call : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ =
    .call ⟨.l110b80,b,n⟩ (callFrame resume ret)
  widths : ParseSignature.ArgumentWidths b
  saved : SavedWidths b
  keep : KeepSystem a b
  rsp : b[4] = ⟨64,sp fr - 8⟩
  rsi : b[6].get 64 = slot fr 0x1d0
  rdi : b[7].get 64 = slot fr dst
  rdx : b[2].get 64 = 0x2021a0
  tag : memLoad n (sp fr - 8) 64 = ret
  frame : RamWriteFrame m n (writes fr spans)
  words : WordsAt n (slot fr 0x1d0) 64 x

private theorem slot_eq (fr : Activation) (i : Nat) : slot fr i = sp fr + BitVec.ofNat 64 i := rfl

private theorem selectFour_eq (s : BitVec 8) (a b : Vector (BitVec 64) 4) :
    selectFour s a b = if s = 0 then a else b := by
  apply Vector.ext
  intro i hi
  simp only [selectFour,Vector.getElem_ofFn]
  by_cases h : s = 0 <;> simp only [h, ite_true, ite_false] <;> rfl

local macro "peer_negate_frame" entry:ident : tactic =>
  `(tactic| (
    simp only [BitVec.add_assoc,BitVec.reduceAdd]
    repeat' refine RamWriteFrame.memStore ?_ _ ?_
    exact RamWriteFrame.refl _ _
    all_goals first
      | exact peerInBelow $entry spans (i := 8) (by decide) (by decide)
      | apply peerInSlot $entry (by decide); decide ))

set_option maxHeartbeats 850000 in
set_option maxRecDepth 8192 in
private theorem firstPush {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (s : Context fr a m)
    {u : Vector (BitVec 64) 4} {v3 : BitVec 64} {sgn : BitVec 8}
    (sign : a[0].get 8 = sgn)
    (raw5 : a[5] = ⟨64,v3⟩) (raw12 : a[12] = ⟨64,u[3]⟩) (raw15 : a[15] = ⟨64,sp fr + 0x1d0⟩)
    (w0 : memLoad m (sp fr + 0x58) 64 = u[0])
    (w1 : memLoad m (sp fr + 0x70) 64 = u[1])
    (w2 : memLoad m (sp fr + 0x50) 64 = u[2]) :
    ∃ (b : Registers) (n : Ram), Pushed .l11cbf4 .l11cc3e fr a b m n 0x11cc3e 0x418 u ∧
      memLoad n (sp fr + 0x48) 8 = sgn ∧
      b[3] = ⟨64,u[0]⟩ ∧ b[13] = ⟨64,u[1]⟩ ∧ b[14] = ⟨64,u[2]⟩ ∧
      b[12] = ⟨64,u[3]⟩ ∧ b[5] = ⟨64,v3⟩ ∧ b[15] = ⟨64,sp fr + 0x1d0⟩ := by
  have access := peerStackAccess e s.frame
  have win : Writable Extracted.programImage m (sp fr) 3256 := by
    simpa only [slot_eq, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      peerSlotWrite e access (i := 0) (n := 3256) (by decide)
  have below : Writable Extracted.programImage m (sp fr - 8) 8 :=
    peerStackBelowWrite e access (off := 8) (by decide)
  have room := e.room
  have hs := peerSpNat e
  have limit := win.readable.low
  have r4 : a[4].get 64 = sp fr := congrArg (Value.get 64) s.atoms.1
  have r12 : a[12].get 64 = u[3] := congrArg (Value.get 64) raw12
  have r15 : a[15].get 64 = sp fr + 0x1d0 := congrArg (Value.get 64) raw15
  have byte : (a[0].get 64).setWidth 8 = sgn := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using sign
  let prior := memStore m (sp fr + 0x48) sgn
  let q := memStore (storeFour prior (sp fr + 0x1d0) u) (sp fr - 8) (0x11cc3e : BitVec 64)
  refine ⟨?b,q,⟨?run,?widths,?saved,?keep,?rsp,?rsi,?rdi,?rdx,?tag,?frame,?words⟩,?sign,
    ?b3,?b13,?b14,?b12,?b5,?b15⟩
  case run =>
    dsimp only [q,prior,storeFour]
    arithmetic_segment using code_l11cbf4 [r4,r12,r15,w0,w1,w2,byte,
      BitVec.add_assoc,BitVec.reduceAdd]
    done
  case widths =>
    intro ⟨i, hi⟩ h
    have old := s.widths ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact old
  case saved =>
    intro ⟨i, hi⟩ h
    have old := s.savedWidths ⟨i, hi⟩ h
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact old
  case keep =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> rfl
  case frame => dsimp only [q,prior,storeFour]; peer_negate_frame e
  case words =>
    dsimp only [q,prior,storeFour]
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl
    all_goals
      simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        slot_eq, BitVec.add_assoc, BitVec.reduceAdd]
      segment_words [] <;> rfl
  case tag => dsimp only [q,prior,storeFour]; segment_words [] <;> rfl
  case sign => dsimp only [q,prior,storeFour]; segment_words [] <;> rfl
  all_goals first | rfl | exact raw5 | exact raw12 | exact raw15

private theorem argument_saved {a : Registers} (saved : SavedWidths a)
    (i : Fin Reg.count) (h : i.val ∈ Activation.calleeSavedNumbers) :
    (⟨64,a[i].get 64⟩ : Value) = a[i] := by
  have w := saved i h
  generalize a[i] = v at w ⊢
  cases v with | mk n x => cases w; rfl

set_option maxHeartbeats 600000 in
private theorem runChild {fr : Activation} {init a b : Registers} {m n : Ram} {d dst x : Nat} {peer : Projective}
    {l resume : Label} {ret : BitVec 64}
    (e : PeerCoreEntry fr init d peer) (s : Context fr a m)
    (p : Pushed l resume fr a b m n ret dst (scalarWords x)) (bound : x < domain.n) (tagSmall : ret.toNat < 2^32)
    (dstRoom : dst+32 ≤ 3208) (apart : dst+32 ≤ 0x1d0 ∨ 0x1f0 ≤ dst)
    (dstSpan : (dst,32) ∈ spans) :
    ∃ c q, Reaches l a m resume c q ∧ Context fr c q ∧
      RamWriteFrame n q (writes fr [(dst,32)]) ∧
      RamWriteFrame m q (writes fr spans) ∧
      WordsAt q (slot fr dst) 64 (negative x) ∧
      (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → c[i] = b[i]) := by
  have whole := s.frame.trans p.frame (peerWithin e (by decide))
  let c := child fr b n ret
  have cs : c.rsi = slot fr 0x1d0 := p.rsi
  have cd : c.rdi = slot fr dst := p.rdi
  have cp : c.rsp = sp fr - 8 := rfl
  have ⟨sp0,df,mx,ft,fc,_⟩ := s.atoms
  have atom : Atom.All Extracted.programImage b n (Fn110b80.frameAt .l110b80 c) :=
    peerChildEntry e Fn110b80.frameInfo rfl (by decide) p.widths p.saved p.rsp
      ((p.keep 22 (by decide)).trans df) ((p.keep 39 (by decide)).trans mx)
      ((p.keep 50 (by decide)).trans ft) ((p.keep 51 (by decide)).trans fc) whole p.tag tagSmall
  have access := peerStackAccess e whole
  have src := (peerSlotWrite e access (i := 0x1d0) (n := 32) (by decide)).readable
  have wr := peerSlotWrite e access (i := dst) (n := 32) (by omega)
  have hp : (sp fr - 8).toNat = (sp fr).toNat - 8 := peerPushNat e
  have ho : (slot fr dst).toNat = (sp fr).toNat + dst := peerSlotNat e dst (by omega)
  have hi : (slot fr 0x1d0).toNat = (sp fr).toNat + 0x1d0 := peerSlotNat e 0x1d0 (by decide)
  have stackNat : (sp fr).toNat = fr.rsp.toNat - 3256 := peerSpNat e
  have room := e.room
  have near : (sp fr - 8).toNat + 8 = (sp fr).toNat := by rw [hp, stackNat]; omega
  have high : c.rsp.toNat + 8 ≤ c.rsi.toNat ∧ c.rsp.toNat + 8 ≤ c.rdi.toNat := by
    rw [cp, cs, cd, near, ho, hi]
    exact ⟨Nat.le_add_right ..,Nat.le_add_right ..⟩
  obtain ⟨out, exec, tag, done_, widths, foot, words⟩ :=
    scalarNegCall atom (e.loaded_of_frame (coreFrame whole)) (cs ▸ src) (cd ▸ wr)
      high.1 high.2 (by rw [cs, cd, hi, ho]; omega) p.rdx bound (cs ▸ p.words)
  rw [cp, cd] at foot
  rw [cd] at words
  have childFrame : RamWriteFrame n out.store (writes fr [(dst,32)]) :=
    (RamWriteFrame.refl _ _).trans foot
      (peerChildWithin e (i := dst) (size := 32) (depth := 48) (by decide) (by omega)
        ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩)
  have resultFrame : RamWriteFrame m out.store (writes fr spans) :=
    p.frame.trans foot (peerChildWithin e (i := dst) (size := 32) (depth := 48) (by decide) (by omega)
      ⟨_, dstSpan, Nat.le_refl _, Nat.le_refl _⟩)
  obtain ⟨rs,df',bx,bp,r12,r13,r14,r15,mx',ft',fc',_⟩ := done_
  have retSp : out.values[4] = a[4] := by
    change out.values[4] = ⟨64,c.rsp + 8⟩ at rs
    rw [rs, cp, BitVec.sub_add_cancel]
    exact sp0.symm
  have savedEq : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → out.values[i] = b[i] := by
    intro i h
    have h' := argument_saved p.saved i h
    rcases i with ⟨i,hi⟩
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact bx.trans h' | exact bp.trans h' | exact r12.trans h' |
        exact r13.trans h' | exact r14.trans h' | exact r15.trans h'
  have saved : SavedWidths out.values := by
    intro i h
    rw [savedEq i h]; exact p.saved i h
  have keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → out.values[i] = a[i] := by
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl
    · exact retSp
    · exact df'.trans df.symm
    · exact mx'.trans mx.symm
    · exact ft'.trans ft.symm
    · exact fc'.trans fc.symm
  refine ⟨out.values,out.store,Sample.reachesAfterSampleCall p.call exec tag [],?_,childFrame,
    resultFrame,words,savedEq⟩
  exact s.peerAdvance e resultFrame (by decide) (by decide) widths saved keep

private theorem word_slot (fr : Activation) (j i : Nat) :
    wordAddr (slot fr j) 64 i = sp fr + BitVec.ofNat 64 (j + 8*i) := by
  rw [slot_eq]
  change (sp fr + BitVec.ofNat 64 j) + BitVec.ofNat 64 (8*i) = _
  rw [BitVec.ofNat_add, BitVec.add_assoc]

private theorem storeFourFrame {fr : Activation} {initial : Registers} {m n : Ram} {d i : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (h : RamWriteFrame m n (writes fr spans))
    (bound : i+32 ≤ 9500) (covered : (i,32) ∈ spans) (w : Vector (BitVec 64) 4) :
    RamWriteFrame m (storeFour n (slot fr i) w) (writes fr spans) := by
  have addr (k : Nat) : slot fr i + BitVec.ofNat 64 k = slot fr (i+k) := by
    simp only [slot_eq, BitVec.ofNat_add, BitVec.add_assoc]
  have inside (k : Nat) (hk : k+8 ≤ 32) :
      InRegions (writes fr spans) (slot fr i + BitVec.ofNat 64 k) 8 := by
    rw [addr]
    exact peerInSlot e (by omega) ⟨(i,32),covered,by dsimp only; omega, by dsimp only; omega⟩
  have first := inside 0 (by decide)
  rw [show slot fr i + BitVec.ofNat 64 0 = slot fr i from BitVec.add_zero _] at first
  exact (((h.memStore w[0] first).memStore w[1] (inside 8 (by decide))).memStore w[2]
    (inside 16 (by decide))).memStore w[3] (inside 24 (by decide))

private theorem selectFrame {fr : Activation} {initial : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (sgn : BitVec 8) (raw negated : Vector (BitVec 64) 4) :
    RamWriteFrame m (selectedMemory m (sp fr) sgn raw negated) (writes fr spans) := by
  have loc := peerInSlot (xs := spans) (i := 0x1d0) (size := 1) e (by decide)
    ⟨(0x1d0,32),by decide,by decide,by decide⟩
  have first := (RamWriteFrame.refl m (writes fr spans)).memStore sgn loc
  exact storeFourFrame e first (i := 0x270) (by decide) (by decide) (selectFour sgn raw negated)

private structure Staged (fr : Activation) (m n : Ram) (v magnitude : Vector (BitVec 64) 4)
    (sign : BitVec 8) : Prop where
  frame : RamWriteFrame m n (writes fr spans)
  tag : memLoad n (sp fr - 8) 64 = 0x11ccfd
  source : WordsAt n (slot fr 0x1d0) 64 v
  mag : WordsAt n (slot fr 0x270) 64 magnitude
  sign : memLoad n (sp fr + 0x48) 8 = sign

set_option maxHeartbeats 500000 in
private theorem secondMemory {fr : Activation} {initial : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (v raw negated : Vector (BitVec 64) 4) (sgn : BitVec 8) {second : BitVec 8}
    (sign : memLoad m (sp fr + 0x48) 8 = second) :
    Staged fr m (dispatchMemory (selectedMemory m (sp fr) sgn raw negated) (sp fr) v)
      v (selectFour sgn raw negated) second := by
  have access := peerStackAccess e (RamWriteFrame.refl fr.original [fr.region])
  have hs := peerSpNat e
  have room := e.room
  have hi := e.high
  have low := Split.Caller.peerLowNat e
  have win : Writable Extracted.programImage fr.original (sp fr) 3256 := by
    simpa only [slot_eq, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      peerSlotWrite e access (i := 0) (n := 3256) (by decide)
  have below : Writable Extracted.programImage fr.original (sp fr - 8) 8 :=
    peerStackBelowWrite e access (off := 8) (by decide)
  refine ⟨?frame,?tag,?source,?mag,?sign⟩
  case frame =>
    exact (storeFourFrame e (selectFrame e sgn raw negated) (i := 0x1d0) (by decide) (by decide) v).memStore
      (0x11ccfd : BitVec 64) (peerInBelow e spans (i := 8) (by decide) (by decide))
  case tag =>
    simp only [dispatchMemory]
    rw [memLoad_memStore_same] <;> decide
  case sign =>
    dsimp only [dispatchMemory,selectedMemory,storeFour]
    simp only [BitVec.add_assoc,BitVec.reduceAdd]
    segment_words [sign]
  case source =>
    dsimp only [dispatchMemory,selectedMemory,storeFour]
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl
    all_goals
      simp only [word_slot,Nat.reduceAdd,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
      segment_words [] <;> rfl
  case mag =>
    dsimp only [dispatchMemory,selectedMemory,storeFour]
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl
    all_goals
      simp only [word_slot,Nat.reduceAdd,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
      segment_words [] <;> rfl

private theorem dispatchSaved {a b : Registers} {base : BitVec 64} {v : Vector (BitVec 64) 4}
    (h : Dispatched a b base v) (old : SavedWidths a) : SavedWidths b := by
  intro ⟨i, hi⟩ hm
  have w := old ⟨i, hi⟩ hm
  simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact congrArg Value.width h.mask
    | exact (congrArg Value.width h.rbp).trans w
    | exact congrArg Value.width h.v0
    | exact congrArg Value.width h.v1
    | exact congrArg Value.width h.v2
    | exact (congrArg Value.width h.work).trans w

set_option maxHeartbeats 500000 in
private theorem secondPush {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (s : Context fr a m)
    {u v negU : Vector (BitVec 64) 4} {sign₁ sign₂ : BitVec 8}
    (sign : memLoad m (sp fr + 0x30) 8 = sign₁)
    (secondSign : memLoad m (sp fr + 0x48) 8 = sign₂)
    (neg : WordsAt m (slot fr 0x418) 64 negU)
    (raw3 : a[3] = ⟨64,u[0]⟩) (raw13 : a[13] = ⟨64,u[1]⟩)
    (raw14 : a[14] = ⟨64,u[2]⟩) (raw12 : a[12] = ⟨64,u[3]⟩)
    (raw5 : a[5] = ⟨64,v[3]⟩) (raw15 : a[15] = ⟨64,sp fr + 0x1d0⟩)
    (w0 : memLoad m (sp fr + 0xa8) 64 = v[0])
    (w1 : memLoad m (sp fr + 0x40) 64 = v[1])
    (w2 : memLoad m (sp fr + 0x10) 64 = v[2]) :
    ∃ (b : Registers) (n : Ram), Pushed .l11cc3e .l11ccfd fr a b m n 0x11ccfd 0x128 v ∧
      memLoad n (sp fr + 0x48) 8 = sign₂ ∧
      WordsAt n (slot fr 0x270) 64 (selectFour sign₁ u negU) ∧
      b[12] = ⟨64,v[0]⟩ ∧ b[13] = ⟨64,v[1]⟩ ∧ b[14] = ⟨64,v[2]⟩ ∧
      b[5] = ⟨64,v[3]⟩ ∧ b[3] = ⟨64,0x3ffffffffffffc⟩ ∧ b[15] = ⟨64,sp fr + 0x1d0⟩ := by
  have access := peerStackAccess e s.frame
  have win : Writable Extracted.programImage m (sp fr) 3256 := by
    simpa only [slot_eq, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      peerSlotWrite e access (i := 0) (n := 3256) (by decide)
  have below : Writable Extracted.programImage m (sp fr - 8) 8 :=
    peerStackBelowWrite e access (off := 8) (by decide)
  have r4 : a[4].get 64 = sp fr := congrArg (Value.get 64) s.atoms.1
  have r3 : a[3].get 64 = u[0] := congrArg (Value.get 64) raw3
  have r12 : a[12].get 64 = u[3] := congrArg (Value.get 64) raw12
  have r13 : a[13].get 64 = u[1] := congrArg (Value.get 64) raw13
  have r14 : a[14].get 64 = u[2] := congrArg (Value.get 64) raw14
  have r5 : a[5].get 64 = v[3] := congrArg (Value.get 64) raw5
  have r15 : a[15].get 64 = sp fr + 0x1d0 := by
    rw [raw15, Value.get_mk_setWidth, BitVec.setWidth_eq]
  obtain ⟨p,hselect,hpre,mask,cx⟩ :=
    selectPrefix (raw := u) (negated := negU) win r4 r3 r13 r14 r12 sign neg
  let n := selectedMemory m (sp fr) sign₁ u negU
  have frame := selectFrame (m := m) e sign₁ u negU
  have sp' := (congrArg (Value.get 64) (hpre.2 4 (by decide) (by decide))).trans r4
  have w3' := (congrArg (Value.get 64) (hpre.2 5 (by decide) (by decide))).trans r5
  have src' := (congrArg (Value.get 64) (hpre.2 15 (by decide) (by decide))).trans r15
  have w0' : memLoad n (sp fr + 0xa8) 64 = v[0] :=
    (frame.memLoad_eq (peerOutside e spans (i := 0xa8) (n := 8) (by decide) (by decide))).trans w0
  have w1' : memLoad n (sp fr + 0x40) 64 = v[1] :=
    (frame.memLoad_eq (peerOutside e spans (i := 0x40) (n := 8) (by decide) (by decide))).trans w1
  have w2' : memLoad n (sp fr + 0x10) 64 = v[2] :=
    (frame.memLoad_eq (peerOutside e spans (i := 0x10) (n := 8) (by decide) (by decide))).trans w2
  obtain ⟨b,hcall,hs⟩ := dispatchTail (v := v) (win.of_frame frame) (below.of_frame frame) hpre s.widths
    sp' w3' src' mask cx w0' w1' w2'
  have run : program.runBlock (dialect Extracted.programImage) ⟨.l11cc3e,a,m⟩ =
      .call ⟨.l110b80,b,dispatchMemory n (sp fr) v⟩ (callFrame .l11ccfd 0x11ccfd) := hselect.trans hcall
  have mem := secondMemory e v u negU sign₁ secondSign
  exact ⟨b,_,⟨run,hs.widths,dispatchSaved hs s.savedWidths,hs.keep,hs.rsp,hs.rsi,hs.rdi,hs.rdx,
    mem.tag,mem.frame,mem.source⟩,mem.sign,mem.mag,hs.v0,hs.v1,hs.v2,hs.rbp.trans raw5,hs.mask,hs.work.trans raw15⟩

attribute [local irreducible] Curve.splitFirst Curve.splitSecond Curve.centered

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
theorem peerNegate {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (s : PeerCompared fr a m d peer) :
    ∃ b n, Reaches .l11cbf4 a m .l11ccfd b n ∧ PeerNegated fr b n d peer := by
  have hn : 0 < domain.n := by decide +kernel
  have hu : Curve.splitFirst d < domain.n := by unfold Curve.splitFirst; exact Nat.mod_lt _ hn
  have hv : Curve.splitSecond d < domain.n := by unfold Curve.splitSecond; exact Nat.mod_lt _ hn
  have u0 := s.slots (0x58,(u d)[0]) (by exact List.mem_cons_self ..)
  have u1 := s.slots (0x70,(u d)[1]) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have u2 := s.slots (0x50,(u d)[2]) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨b,p,first,sign₂,b3,b13,b14,b12,b5,b15⟩ := firstPush e s.toContext (u := u d) s.secondSign s.r5 s.r12 s.r15
    u0 u1 u2
  obtain ⟨c,q,path₁,ctx₁,callee₁,frame₁,result₁,keep₁⟩ :=
    runChild e s.toContext (x := Curve.splitFirst d) first hu (by decide) (by decide) (by decide) (by decide)
  have sign₁ : memLoad q (sp fr + 0x30) 8 = flag (firstComponent d) :=
    (frame₁.memLoad_eq (peerOutside e spans (i := 0x30) (n := 1) (by decide) (by decide))).trans s.firstSign
  have w0 : memLoad q (sp fr + 0xa8) 64 = (v d)[0] :=
    (frame₁.memLoad_eq (peerOutside e spans (i := 0xa8) (n := 8) (by decide) (by decide))).trans
      (s.slots (0xa8,(v d)[0]) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have w1 : memLoad q (sp fr + 0x40) 64 = (v d)[1] :=
    (frame₁.memLoad_eq (peerOutside e spans (i := 0x40) (n := 8) (by decide) (by decide))).trans
      (s.slots (0x40,(v d)[1]) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  have w2 : memLoad q (sp fr + 0x10) 64 = (v d)[2] :=
    (frame₁.memLoad_eq (peerOutside e spans (i := 0x10) (n := 8) (by decide) (by decide))).trans
      (s.slots (0x10,(v d)[2]) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
  have sign₂q : memLoad q (sp fr + 0x48) 8 = flag (secondComponent d) :=
    (callee₁.memLoad_eq (peerOutside e [(0x418,32)] (i := 0x48) (n := 1) (by decide) (by decide))).trans sign₂
  obtain ⟨f,r,second,sign₂r,mag,f12,f13,f14,f5,f3,f15⟩ := secondPush e ctx₁ (u := u d) (v := v d) sign₁ sign₂q result₁
    ((keep₁ 3 (by decide)).trans b3) ((keep₁ 13 (by decide)).trans b13)
    ((keep₁ 14 (by decide)).trans b14) ((keep₁ 12 (by decide)).trans b12)
    ((keep₁ 5 (by decide)).trans b5) ((keep₁ 15 (by decide)).trans b15) w0 w1 w2
  have hMag : selectFour (flag (firstComponent d)) (u d) (negative (Curve.splitFirst d)) =
      scalarWords (firstComponent d).natAbs := (selectFour_eq _ _ _).trans (selectMagnitude hu)
  rw [hMag] at mag
  obtain ⟨g,t,path₂,ctx₂,callee₂,frame₂,result₂,keep₂⟩ :=
    runChild e ctx₁ (x := Curve.splitSecond d) second hv (by decide) (by decide) (by decide) (by decide)
  have firstSign : memLoad t (sp fr + 0x30) 8 = flag (firstComponent d) :=
    (frame₂.memLoad_eq (peerOutside e spans (i := 0x30) (n := 1) (by decide) (by decide))).trans sign₁
  have secondSign : memLoad t (sp fr + 0x48) 8 = flag (secondComponent d) :=
    (callee₂.memLoad_eq (peerOutside e [(0x128,32)] (i := 0x48) (n := 1) (by decide) (by decide))).trans sign₂r
  have mag' : WordsAt t (sp fr + 0x270) 64 (scalarWords (firstComponent d).natAbs) := by
    intro i hi
    have addr : wordAddr (sp fr + 0x270) 64 i = slot fr (0x270+8*i) :=
      (word_slot fr 0x270 i).trans (slot_eq fr _).symm
    exact (callee₂.memLoad_eq (by
      rw [addr]
      apply peerOutside e [(0x128,32)] (by omega)
      intro x h
      obtain rfl := List.mem_singleton.mp h
      exact Or.inr (by change 0x128+32 ≤ 0x270+8*i; omega))).trans (mag i hi)
  exact ⟨g,t,path₁.trans path₂,ctx₂,peerKeepEndo e (peerKeepEndo e s.endo frame₁ (by decide)) frame₂ (by decide),
    firstSign,secondSign,mag',result₂,(keep₂ 12 (by decide)).trans f12,(keep₂ 13 (by decide)).trans f13,
    (keep₂ 14 (by decide)).trans f14,(keep₂ 5 (by decide)).trans f5,(keep₂ 3 (by decide)).trans f3,
    (keep₂ 15 (by decide)).trans f15⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
