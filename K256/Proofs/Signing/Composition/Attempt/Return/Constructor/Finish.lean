import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.State
import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Signing.Composition.Attempt.Return.Constructor

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.DomainParameters.Secp256k1 Signing.LIR
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Sec1.Serialize.Assemble (fourWordsAt wordsAtOffset)

private abbrev image := Extracted.programImage
private abbrev Window (p : BitVec 64) (m : Ram) := Writable image m (p-9) 313
private abbrev area (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-9).toNat,137⟩,⟨(p+232).toNat,72⟩]
private abbrev Keeps (a b : Registers) :=
  ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]

private theorem windowOffset {p addr : BitVec 64} {m : Ram} {n : Nat} (win : Window p m)
    (fit : (addr-(p-9)).toNat+n ≤ 313) :
    addr.toNat = (p-9).toNat + (addr-(p-9)).toNat := by
  have low := win.readable.low
  calc
    _ = (((p-9) + (addr-(p-9)) : BitVec 64)).toNat :=
      congrArg BitVec.toNat (by bv_omega)
    _ = _ := by rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]

private theorem windowSlot {p addr : BitVec 64} {m : Ram} {n : Nat} (win : Window p m)
    (fit : (addr-(p-9)).toNat+n ≤ 313)
    (which : (addr-(p-9)).toNat+n ≤ 137 ∨ 241 ≤ (addr-(p-9)).toNat) :
    InRegions (area p) addr n := by
  have low := win.readable.low
  have address := windowOffset win fit
  have outOffset : p+232-(p-9) = 241 := by bv_omega
  have output := windowOffset win (addr := p+232) (n := 72) (by rw [outOffset]; decide)
  rw [outOffset] at output
  change (p+232).toNat = (p-9).toNat + 241 at output
  rcases which with lower | upper
  · refine ⟨_,List.mem_cons_self,?_⟩
    change (p-9).toNat ≤ addr.toNat ∧ addr.toNat+n ≤ (p-9).toNat+137 ∧ addr.toNat+n ≤ 2^64
    omega
  · refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
    change (p+232).toNat ≤ addr.toNat ∧ addr.toNat+n ≤ (p+232).toNat+72 ∧ addr.toNat+n ≤ 2^64
    omega

local macro "constructor_slot" win:ident p:ident : tactic => `(tactic|
  (apply windowSlot $win <;>
    simp only [addr_sub $p 8,addr_sub $p 9,add_sub_add_left',
      show $p-($p+(0-9)) = 9 by bv_omega,BitVec.reduceToNat] <;> decide))

private theorem callReach {caller callee : Location Value Ram Label signature} {retLabel : Label}
    {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (call : program.runBlock (dialect image) caller = .call callee (resume retLabel ret))
    (exec : program.Exec (dialect image) ⟨callee,[]⟩ out) (tag : out.tag = some ⟨64,ret⟩) :
    Reach ⟨caller,[resume .l105d35 0x105d35,resume .l102795 0x102795]⟩
      (inside retLabel out.values out.store) := by
  refine .step (b := ⟨callee,[resume retLabel ret,resume .l105d35 0x105d35,resume .l102795 0x102795]⟩)
    ?_ (ParseSignature.exec_reaches_resume exec _ _ ?_)
  · exact congrArg (Transfer.next (dialect image) [resume .l105d35 0x105d35,resume .l102795 0x102795]) call
  · rw [tag]
    exact decide_eq_true rfl

private theorem zeroWords {x : Nat} (bound : x < domain.n) :
    (∀ i (hi : i < 4), (scalarWords x)[i] = 0) ↔ x = 0 := by
  constructor
  · intro eq
    have hv := Generate.Generator.Multiply.Split.scalarWords_value x (Nat.lt_trans bound (by decide +kernel))
    rw [← hv]
    simp only [Generate.Generator.Multiply.Split.scalarValue,eq 0 (by decide),eq 1 (by decide),
      eq 2 (by decide),eq 3 (by decide)]
    rfl
  · rintro rfl i hi
    simp only [scalarWords,Vector.getElem_ofFn,Nat.zero_div]
    rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem stageS {a : Registers} {m : Ram} {p : BitVec 64} {w : Vector (BitVec 64) 4}
    (win : Writable Extracted.programImage m (p-9) 313) (rsp : a[4] = ⟨64,p⟩) (words : WordsAt m (p+8) 64 w) :
    ∃ b n, program.runBlock (dialect image) ⟨.l103515,a,m⟩ =
        .call ⟨.l127f50,b,n⟩ (resume .l103577 0x103577) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+64⟩ ∧ b[2] = ⟨64,p⟩ ∧
      b[6] = ⟨64,4⟩ ∧ b[1] = ⟨64,4⟩ ∧ b[8] = a[8] ∧ b[9] = a[9] ∧ Keeps a b ∧
      RamWriteFrame m n (area p) ∧ memLoad n (p-8) 64 = 0x103577 ∧
      WordsAt n p 64 (Vector.replicate 4 0) ∧ WordsAt n (p+96) 64 w ∧
      (∀ i (_hi : i < 4), memLoad n (wordAddr (p+64) 64 i) 64 =
        memLoad m (wordAddr (p+64) 64 i) 64) := by
  have gsp : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have w0 : memLoad m (p+8) 64 = w[0] := wordsAtOffset words 0 (by decide)
  have w1 : memLoad m (p+16) 64 = w[1] := wordsAtOffset words 1 (by decide)
  have w2 : memLoad m (p+24) 64 = w[2] := wordsAtOffset words 2 (by decide)
  have w3 : memLoad m (p+32) 64 = w[3] := wordsAtOffset words 3 (by decide)
  refine ⟨?_,?_,?run,?g4,?g7,?g2,?g6,?g1,?g8,?g9,?keeps,?frame,?tag,?zero,?copy,?unchanged⟩
  case run =>
    cfg_eval [gsp]
    segment_words []
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l103515)
    rfl
  case g4 | g7 | g2 | g6 | g1 | g8 | g9 => rfl
  case keeps =>
    intro ⟨i,hi⟩ mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case frame =>
    iterate 9 refine RamWriteFrame.memStore ?_ _ (by constructor_slot win p)
    exact .refl _ _
  case tag => segment_words []
  case zero => apply fourWordsAt <;> (segment_words []; rfl)
  case copy => apply fourWordsAt <;> segment_words [w0,w1,w2,w3]
  case unchanged =>
    intro i hi
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals segment_words [wordAddr, Nat.reduceDiv, Nat.reduceMul]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
private theorem stageR {a : Registers} {m : Ram} {p : BitVec 64}
    (win : Writable Extracted.programImage m (p-9) 313) (rsp : a[4] = ⟨64,p⟩) :
    ∃ b n, program.runBlock (dialect image) ⟨.l103585,a,m⟩ =
        .call ⟨.l127f50,b,n⟩ (resume .l1035bf 0x1035bf) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+96⟩ ∧ b[2] = ⟨64,p⟩ ∧
      b[6] = ⟨64,4⟩ ∧ b[1] = ⟨64,4⟩ ∧ b[8] = a[8] ∧ b[9] = a[9] ∧ Keeps a b ∧
      RamWriteFrame m n (area p) ∧ memLoad n (p-8) 64 = 0x1035bf ∧
      WordsAt n p 64 (Vector.replicate 4 0) ∧ RamWriteFrame m n [⟨(p-8).toNat,40⟩] := by
  have gsp : a[4].get 64 = p := congrArg (Value.get 64) rsp
  refine ⟨?_,?_,?run,?g4,?g7,?g2,?g6,?g1,?g8,?g9,?keeps,?frame,?tag,?zero,?scratch⟩
  case run =>
    cfg_eval [gsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l103585)
    rfl
  case g4 | g7 | g2 | g6 | g1 | g8 | g9 => rfl
  case keeps =>
    intro ⟨i,hi⟩ mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case frame =>
    iterate 5 refine RamWriteFrame.memStore ?_ _ (by constructor_slot win p)
    exact .refl _ _
  case tag => segment_words []
  case zero => apply fourWordsAt <;> (segment_words []; rfl)
  case scratch =>
    have sub := win.of_offsets (n := 40) (addr_sub p 8) (addr_sub p 9) (by decide)
    iterate 5 refine RamWriteFrame.memStore ?_ _ ?_
    · exact .refl _ _
    all_goals
      refine ⟨_,List.mem_singleton_self _,?_⟩
      have low := sub.readable.low
      simp only [InRegion,BitVec.toNat_add,BitVec.toNat_sub,BitVec.reduceToNat] at *
      omega

private theorem widthValue (v : Value) (w : Nat) (h : v.width = w) :
    v = ⟨w,v.get w⟩ := by
  cases v
  cases h
  simp only [Value.get_mk]

private theorem compareReturn {p left ret : BitVec 64} {a b : Registers} {m n : Ram}
    {label retLabel : Label}
    (call : program.runBlock (dialect image) ⟨label,a,m⟩ =
      .call ⟨.l127f50,b,n⟩ (resume retLabel ret))
    (win : Window p n) (rsp : b[4] = ⟨64,p-8⟩) (di : b[7] = ⟨64,left⟩)
    (dx : b[2] = ⟨64,p⟩) (si : b[6] = ⟨64,4⟩) (cx : b[1] = ⟨64,4⟩)
    (leftRead : Readable n left 32)
    (calleeWidths : ∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15] → b[i].width = 64)
    (df : b[22] = ⟨1,0⟩) (fp : b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16)
    (returnSlot : memLoad n (p-8) 64 = ret) (retLow : ret.toNat < 2^32)
    (alignment : (p-8).toNat % 16 = 8) :
    ∃ c, Reach (inside label a m) (inside retLabel c n) ∧
      c[4] = ⟨64,p⟩ ∧ Keeps b c ∧ ParseSignature.ArgumentWidths c ∧
      (c[0].get 8 = 1 ↔ ∀ i < 4, memLoad n (wordAddr left 64 i) 64 = memLoad n (wordAddr p 64 i) 64) ∧
      (c[0].get 8 = 0 ∨ c[0].get 8 = 1) := by
  let fr : Activation := {
    original := n, rsp := p-8, low := p-8, ret := ret
    rdi := left, rsi := 4, rdx := p, rcx := 4
    rbx := b[3].get 64, rbp := b[5].get 64, r8 := b[8].get 64, r9 := b[9].get 64
    r12 := b[12].get 64, r13 := b[13].get 64, r14 := b[14].get 64, r15 := b[15].get 64
    mxcsr := b[39].get 32, ftw := b[50].get 16, fcw := b[51].get 16, fs := default }
  have scalarReg (i : Fin Reg.count) (h : i.val ∈ [3,5,8,9,12,13,14,15]) :
      b[i] = ⟨64,b[i].get 64⟩ := widthValue _ _ (calleeWidths i h)
  have entry : Atom.All image b n (Proofs.LIR.Fn127f50.frameAt .l127f50 fr) := by
    have slot := win.readable.of_offsets (n := 8) (addr_sub p 8) (addr_sub p 9) (by decide)
    exact ⟨rsp,df,cx,dx,scalarReg 3 (by decide),scalarReg 5 (by decide),si,di,
      scalarReg 8 (by decide),scalarReg 9 (by decide),scalarReg 12 (by decide),scalarReg 13 (by decide),
      scalarReg 14 (by decide),scalarReg 15 (by decide),widthValue _ _ fp.1,
      widthValue _ _ fp.2.1,widthValue _ _ fp.2.2,slot,returnSlot,retLow,Nat.le_refl _,alignment,trivial⟩
  obtain ⟨out,exec,tag,doneAtoms,_,widths,same,equal,binary⟩ :=
    Generate.Generator.Sample.ctEq_call Common.fnCode_subset_programImage fr rfl rfl leftRead
      (win.readable.of_offsets (addr_self p) (addr_sub p 9) (by decide)) b entry
  have verify := Verify.Transfer.compareExec (dst := .l127f50) rfl exec
  have reached := callReach call (Signing.Transfer.verifyExecAt rfl verify) tag
  change out.store = n at same
  rw [same] at reached
  rw [← Proofs.LIR.Fn127f50.doneAt_canonical] at doneAtoms
  simp only [Proofs.LIR.Fn127f50.doneAt, Atom.All, Atom.Holds] at doneAtoms
  obtain ⟨osp,odf,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := doneAtoms
  refine ⟨out.values,reached,?stack,?keeps,widths,equal,binary⟩
  case stack =>
    change out.values[4] = ⟨64,p-8+8⟩ at osp
    rwa [BitVec.sub_add_cancel] at osp
  case keeps =>
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact bx.trans (scalarReg 3 (by decide)).symm
    · exact bp.trans (scalarReg 5 (by decide)).symm
    · exact r12.trans (scalarReg 12 (by decide)).symm
    · exact r13.trans (scalarReg 13 (by decide)).symm
    · exact r14.trans (scalarReg 14 (by decide)).symm
    · exact r15.trans (scalarReg 15 (by decide)).symm
    · exact odf.trans df.symm
    · exact mx.trans (widthValue _ _ fp.1).symm
    · exact ft.trans (widthValue _ _ fp.2.1).symm
    · exact fc.trans (widthValue _ _ fp.2.2).symm

private theorem stageKeepsWidths {a b : Registers}
    (keep : Keeps a b) (w8 : b[8] = a[8]) (w9 : b[9] = a[9])
    (sized : ∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15] → a[i].width = 64) :
    ∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15] → b[i].width = 64 := by
  intro i h
  have eq : b[i] = a[i] := by
    by_cases h8 : i.val = 8
    · have e : i = 8 := Fin.ext h8
      exact e ▸ w8
    by_cases h9 : i.val = 9
    · have e : i = 9 := Fin.ext h9
      exact e ▸ w9
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    omega
  rw [eq]
  exact sized i h

private theorem keepsFp {a b : Registers} (keep : Keeps a b)
    (fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16) :
    b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16 := by
  exact ⟨(congrArg Value.width (keep 39 (by decide))).trans fp.1,
    (congrArg Value.width (keep 50 (by decide))).trans fp.2.1,
    (congrArg Value.width (keep 51 (by decide))).trans fp.2.2⟩

private theorem binaryFlag {v : Value} (binary : v.get 8 = 0 ∨ v.get 8 = 1) :
    ((v.get 64).setWidth 8 &&& 1).setWidth 64 = (v.get 8).setWidth 64 := by
  have low : (v.get 64).setWidth 8 = v.get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
  rw [low]
  rcases binary with h|h <;> rw [h] <;> rfl

private abbrev choiceAddress (secondCheck : Bool) : BitVec 64 :=
  if secondCheck then 0x1035c9 else 0x103581

private abbrev choiceLabel (secondCheck : Bool) : Label :=
  if secondCheck then .l1035c9 else .l103581

set_option maxRecDepth 4096 in
private theorem choiceCall {p : BitVec 64} {a : Registers} {m : Ram} (secondCheck : Bool)
    (win : Writable Extracted.programImage m (p-9) 313) (rsp : a[4] = ⟨64,p⟩) (binary : a[0].get 8 = 0 ∨ a[0].get 8 = 1) :
    ∃ b, program.runBlock (dialect image) ⟨if secondCheck then .l1035bf else .l103577,a,m⟩ =
        .call ⟨.l127d50,b,memStore m (p-8) (choiceAddress secondCheck)⟩
          (resume (choiceLabel secondCheck) (choiceAddress secondCheck)) ∧
      b[4].get 64 = p-8 ∧ b[7].get 64 = (a[0].get 8).setWidth 64 ∧ Keeps a b ∧
      (ParseSignature.ArgumentWidths a → ParseSignature.ArgumentWidths b) := by
  have gsp : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have flag := binaryFlag binary
  cases secondCheck
  · refine ⟨?_,?run,?_,?_,?_,?_⟩
    case run =>
      change program.runBlock (dialect image) ⟨.l103577,a,m⟩ = _
      cfg_eval [gsp]
      refine Eq.trans (ite_eq_left ?_) ?_
      · slot_guard using code_l103577
      · rfl
    all_goals
      first
      | (change (p-8).setWidth 64 = p-8
         exact BitVec.setWidth_eq _)
      | (change (((mergeGPR 8 _ _).setWidth 8).setWidth 64).setWidth 64 = _
         rw [BitVec.setWidth_eq,setWidth_mergeGPR8,flag])
      | (intro ⟨i,hi⟩ h
         simp only [List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
      | (intro orig ⟨i,hi⟩ h
         have prev := orig ⟨i,hi⟩ h
         simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact prev)
  · refine ⟨?_,?run,?_,?_,?_,?_⟩
    case run =>
      change program.runBlock (dialect image) ⟨.l1035bf,a,m⟩ = _
      cfg_eval [gsp]
      refine Eq.trans (ite_eq_left ?_) ?_
      · slot_guard using code_l1035bf
      · rfl
    all_goals
      first
      | (change (p-8).setWidth 64 = p-8
         exact BitVec.setWidth_eq _)
      | (change (((mergeGPR 8 _ _).setWidth 8).setWidth 64).setWidth 64 = _
         rw [BitVec.setWidth_eq,setWidth_mergeGPR8,flag])
      | (intro ⟨i,hi⟩ h
         simp only [List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
      | (intro orig ⟨i,hi⟩ h
         have prev := orig ⟨i,hi⟩ h
         simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact prev)

private theorem choiceReturn {p : BitVec 64} {a : Registers} {m : Ram} (secondCheck : Bool)
    (win : Writable Extracted.programImage m (p-9) 313) (rsp : a[4] = ⟨64,p⟩) (binary : a[0].get 8 = 0 ∨ a[0].get 8 = 1)
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b n, Reach (inside (if secondCheck then .l1035bf else .l103577) a m)
        (inside (choiceLabel secondCheck) b n) ∧ b[4] = ⟨64,p⟩ ∧ Keeps a b ∧
      ParseSignature.ArgumentWidths b ∧ b[0].get 8 = a[0].get 8 ∧
      RamWriteFrame m n (area p) ∧ RamWriteFrame m n [⟨(p-9).toNat,9⟩] := by
  obtain ⟨c,pushed,csp,bit,kept,cWidths⟩ := choiceCall secondCheck win rsp binary
  let ret := choiceAddress secondCheck
  have slot := win.readable.of_offsets (n := 8) (addr_sub p 8) (addr_sub p 9) (by decide)
  have written : memLoad (memStore m (p-8) ret) (p-8) 64 = ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have work : Writable image (memStore m (p-8) ret) (p-8-1) 1 := by
    rw [show p-8-1 = p-9 by bv_omega]
    exact (win.memStore _ _).of_offsets (addr_self _) (addr_self _) (by decide)
  obtain ⟨out,block,tag,osp,flag,changed,survives⟩ := Sec1.Serialize.choiceBlock
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l127d50 x hx))
    csp work (slot.memStore _ _) (by rw [written]; cases secondCheck <;> decide)
  have exec : Sec1.LIR.program.Exec (dialect image)
      ⟨⟨.l127d50,c,memStore m (p-8) ret⟩,[]⟩ out :=
    .done (by simp only [Program.step,block,CFG.Transfer.next])
  have gen : Generate.LIR.program.Exec (dialect image)
      ⟨⟨.l127d50,c,memStore m (p-8) ret⟩,[]⟩ out :=
    Generate.Serialize.Relabel.exec Generate.Serialize.matches_blocks exec rfl
  have verify := Verify.Transfer.compareExec (dst := .l127d50) rfl gen
  rw [written] at tag
  have reach := callReach pushed (Signing.Transfer.verifyExecAt rfl verify) tag
  have start := toNat_of_offsets (n := 8) (addr_sub p 8) (addr_sub p 9) win.readable.low (by decide)
  have pushFrame : RamWriteFrame m (memStore m (p-8) ret) [⟨(p-9).toNat,9⟩] := by
    refine (RamWriteFrame.refl _ _).memStore _ ⟨_,List.mem_singleton_self _,?_⟩
    unfold InRegion
    rw [start]
    have := win.readable.low
    simp only [BitVec.reduceSub,BitVec.reduceToNat]
    omega
  have writes := pushFrame.trans changed (by
    intro r h
    obtain rfl := List.mem_singleton.mp h
    simp only [show p-8-1 = p-9 by bv_omega]
    exact ⟨_,List.mem_singleton_self _,Nat.le_refl _,by dsimp only [MemoryRegion.start,MemoryRegion.size]; omega⟩)
  have total : RamWriteFrame m out.store (area p) :=
    (RamWriteFrame.refl _ _).trans writes (by
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact ⟨_,List.mem_cons_self,Nat.le_refl _,by dsimp only [MemoryRegion.start,MemoryRegion.size]; omega⟩)
  refine ⟨out.values,out.store,reach,?_,?_,?_,?_,total,writes⟩
  · simpa only [BitVec.sub_add_cancel] using osp
  · intro i h
    exact (survives i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      omega)).trans (kept i h)
  · intro i h
    have keep := survives i (by
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      omega)
    rw [keep]
    exact cWidths widths i h
  · rw [flag,bit]
    change (((a[0].get 8).setWidth 64).setWidth 8 |>.setWidth 64).setWidth 8 = _
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]

private abbrev ExitKeeps (a b : Registers) :=
  ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,22,39,50,51] → b[i] = a[i]

private theorem lowTag {m : Ram} {p x : BitVec 64} (tag : memLoad m p 64 = x) :
    memLoad m p 8 = x.extractLsb' 0 8 := by
  have low := extractLsb'_memLoad (n := 64) m p 0 8 (by decide) (by decide) (by decide)
  rw [tag] at low
  exact (congrArg (fun q => memLoad m q 8) (BitVec.add_zero p)).symm.trans low.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
private theorem writeSuccess {a : Registers} {m : Ram} {p : BitVec 64} {r t : Vector (BitVec 64) 4}
    (win : Writable Extracted.programImage m (p-9) 313) (rsp : a[4] = ⟨64,p⟩)
    (dst : a[3] = ⟨64,p+232⟩) (first : WordsAt m (p+64) 64 r)
    (second : WordsAt m (p+96) 64 t) :
    ∃ b n, Reach (inside .l1035ec a m) (inside .l1035dc b n) ∧
      ExitKeeps a b ∧ ParseSignature.ArgumentWidths b ∧ RamWriteFrame m n (area p) ∧
      memLoad n (p+232) 8 = 0 ∧ WordsAt n (p+240) 64 r ∧ WordsAt n (p+272) 64 t := by
  have gsp : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have gdst : a[3].get 64 = p+232 := congrArg (Value.get 64) dst
  have evalBlock : ∃ b n, program.runBlock (dialect image) ⟨.l1035ec,a,m⟩ = .jump ⟨.l1035dc,b,n⟩ ∧
      ExitKeeps a b ∧ ParseSignature.ArgumentWidths b ∧ RamWriteFrame m n (area p) ∧
      memLoad n (p+232) 8 = 0 ∧ WordsAt n (p+240) 64 r ∧ WordsAt n (p+272) 64 t := by
    refine ⟨?_,?_,?run,?keep,?widths,?writes,?tag,?first,?second⟩
    case run =>
      cfg_eval [b_l1035ec_1,gsp,gdst]
      segment_words []
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1035ec)
      rfl
    case keep =>
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    case widths =>
      intro ⟨i,hi⟩ h
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    case writes =>
      iterate 17 refine RamWriteFrame.memStore ?_ _ (by constructor_slot win p)
      exact .refl _ _
    case tag =>
      exact lowTag (x := 0) (by segment_words [])
    case first =>
      apply fourWordsAt <;> segment_words []
      · exact wordsAtOffset first 0 (by decide)
      · exact wordsAtOffset first 1 (by decide)
      · exact wordsAtOffset first 2 (by decide)
      · exact wordsAtOffset first 3 (by decide)
    case second =>
      apply fourWordsAt <;> segment_words []
      · exact wordsAtOffset second 0 (by decide)
      · exact wordsAtOffset second 1 (by decide)
      · exact wordsAtOffset second 2 (by decide)
      · exact wordsAtOffset second 3 (by decide)
  obtain ⟨b,n,run,rest⟩ := evalBlock
  exact ⟨b,n,.single (congrArg (Transfer.next (dialect image) _) run),rest⟩

set_option maxRecDepth 4096 in
private theorem writeFailure {a : Registers} {m : Ram} {p : BitVec 64}
    (win : Writable Extracted.programImage m (p-9) 313) (dst : a[3] = ⟨64,p+232⟩)
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b n, Reach (inside .l1035cd a m) (inside .l1035dc b n) ∧
      ExitKeeps a b ∧ ParseSignature.ArgumentWidths b ∧ RamWriteFrame m n (area p) ∧
      memLoad n (p+232) 8 = 1 ∧ memLoad n (p+240) 64 = 0 := by
  have gdst : a[3].get 64 = p+232 := congrArg (Value.get 64) dst
  have evalBlock : ∃ b n, program.runBlock (dialect image) ⟨.l1035cd,a,m⟩ = .jump ⟨.l1035dc,b,n⟩ ∧
      ExitKeeps a b ∧ ParseSignature.ArgumentWidths b ∧ RamWriteFrame m n (area p) ∧
      memLoad n (p+232) 8 = 1 ∧ memLoad n (p+240) 64 = 0 := by
    refine ⟨?_,?_,?run,?keep,?widths,?writes,?tag,?zero⟩
    case run =>
      cfg_eval [gdst]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1035cd)
      rfl
    case keep =>
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    case widths =>
      intro ⟨i,hi⟩ h
      have orig := widths ⟨i,hi⟩ h
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact orig
    case writes =>
      iterate 2 refine RamWriteFrame.memStore ?_ _ (by constructor_slot win p)
      exact .refl _ _
    case tag => exact lowTag (x := 1) (by segment_words [])
    case zero => segment_words []
  obtain ⟨b,n,run,rest⟩ := evalBlock
  exact ⟨b,n,.single (congrArg (Transfer.next (dialect image) _) run),rest⟩

private abbrev checkTarget (secondCheck isZero : Bool) : Label :=
  if isZero then .l1035cd else if secondCheck then .l1035ec else .l103585

set_option maxRecDepth 4096 in
private theorem testZero {a : Registers} {m : Ram} (secondCheck isZero : Bool)
    (flag : a[0].get 8 = if isZero then 1 else 0) :
    ∃ b, Reach (inside (choiceLabel secondCheck) a m) (inside (checkTarget secondCheck isZero) b m) ∧
      b[4] = a[4] ∧ Keeps a b ∧ (ParseSignature.ArgumentWidths a → ParseSignature.ArgumentWidths b) := by
  have low : (a[0].get 64).setWidth 8 = a[0].get 8 :=
    BitVec.setWidth_setWidth_of_le _ (by decide)
  have evalBlock : ∃ b : Registers, program.runBlock (dialect image) ⟨choiceLabel secondCheck,a,m⟩ =
        .jump ⟨checkTarget secondCheck isZero,b,m⟩ ∧
      b[4] = a[4] ∧ Keeps a b ∧ (ParseSignature.ArgumentWidths a → ParseSignature.ArgumentWidths b) := by
    cases secondCheck <;> cases isZero <;>
      (refine ⟨?_,?_,?_,?_,?_⟩
       rotate_left
       · first
         | (change program.runBlock (dialect image) ⟨.l103581,a,m⟩ = _
            cfg_eval [low,flag]; rfl)
         | (change program.runBlock (dialect image) ⟨.l1035c9,a,m⟩ = _
            cfg_eval [low,flag]; rfl)
       · rfl
       · intro ⟨i,hi⟩ h
         simp only [List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
       · intro widths ⟨i,hi⟩ h
         have orig := widths ⟨i,hi⟩ h
         simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact orig)
  obtain ⟨b,run,rest⟩ := evalBlock
  exact ⟨b,.single (congrArg (Transfer.next (dialect image) _) run),rest⟩

private abbrev ReturnKeeps (a b : Registers) :=
  ∀ i : Fin Reg.count, i.val ∈ [5,12,13,22,39,50,51] → b[i] = a[i]

set_option maxRecDepth 4096 in
private theorem returnBlock {a : Registers} {m : Ram} {p bx r14 r15 : BitVec 64}
    (win : Writable Extracted.programImage m (p-9) 313) (rsp : a[4] = ⟨64,p⟩)
    (savedBx : memLoad m (p+192) 64 = bx) (saved14 : memLoad m (p+200) 64 = r14)
    (saved15 : memLoad m (p+208) 64 = r15) (tag : memLoad m (p+216) 64 = 0x105d35)
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b, Reach (inside .l1035dc a m) (core .l105d35 b m) ∧
      b[4] = ⟨64,p+224⟩ ∧ b[3] = ⟨64,bx⟩ ∧ b[14] = ⟨64,r14⟩ ∧ b[15] = ⟨64,r15⟩ ∧
      ReturnKeeps a b ∧ ParseSignature.ArgumentWidths b := by
  have gsp : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have evalBlock : ∃ out : Output Value Ram Reg.count,
      program.runBlock (dialect image) ⟨.l1035dc,a,m⟩ = .returned out ∧
      out.store = m ∧ out.tag = some ⟨64,0x105d35⟩ ∧
      out.values[4] = ⟨64,p+224⟩ ∧ out.values[3] = ⟨64,bx⟩ ∧
      out.values[14] = ⟨64,r14⟩ ∧ out.values[15] = ⟨64,r15⟩ ∧
      ReturnKeeps a out.values ∧ ParseSignature.ArgumentWidths out.values := by
    refine ⟨?_,?run,?store,?tag,?rsp,?bx,?r14,?r15,?keep,?widths⟩
    case run =>
      cfg_eval [gsp,savedBx,saved14,saved15,tag]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1035dc)
      rfl
    case store | tag | rsp | bx | r14 | r15 => rfl
    case keep =>
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    case widths =>
      intro ⟨i,hi⟩ h
      have orig := widths ⟨i,hi⟩ h
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact orig
  obtain ⟨out,run,store,ret,bsp,bbx,b14,b15,keep,bwidths⟩ := evalBlock
  have reach : Reach (inside .l1035dc a m) (core .l105d35 out.values out.store) := by
    apply Semantics.Reaches.single
    change (program.runBlock (dialect image) ⟨.l1035dc,a,m⟩).next (dialect image)
      [resume .l105d35 0x105d35,resume .l102795 0x102795] = _
    rw [run]
    have accepted : (resume .l105d35 0x105d35).Accepts (dialect image) out.tag = true := by
      rw [ret]
      exact decide_eq_true (rfl : Value.mk 64 0x105d35 = Value.mk 64 0x105d35)
    simp only [CFG.Transfer.next,accepted,↓reduceIte]
    rfl
  exact ⟨out.values,store ▸ reach,bsp,bbx,b14,b15,keep,bwidths⟩

private theorem checkZero {a b : Registers} {m n : Ram} {p left : BitVec 64} {label : Label}
    {x : Nat} (secondCheck : Bool) (bound : x < domain.n)
    (call : program.runBlock (dialect image) ⟨label,a,m⟩ =
      .call ⟨.l127f50,b,n⟩ (resume (if secondCheck then .l1035bf else .l103577)
        (if secondCheck then 0x1035bf else 0x103577)))
    (win : Window p n) (rsp : b[4] = ⟨64,p-8⟩) (di : b[7] = ⟨64,left⟩)
    (dx : b[2] = ⟨64,p⟩) (si : b[6] = ⟨64,4⟩) (cx : b[1] = ⟨64,4⟩)
    (leftRead : Readable n left 32)
    (calleeWidths : ∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15] → b[i].width = 64)
    (df : b[22] = ⟨1,0⟩) (fp : b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16)
    (returnSlot : memLoad n (p-8) 64 = if secondCheck then 0x1035bf else 0x103577)
    (alignment : (p-8).toNat % 16 = 8)
    (leftWords : WordsAt n left 64 (scalarWords x)) (rightWords : WordsAt n p 64 (Vector.replicate 4 0)) :
    ∃ c q, Reach (inside label a m) (inside (checkTarget secondCheck (decide (x=0))) c q) ∧
      c[4] = ⟨64,p⟩ ∧ Keeps b c ∧ ParseSignature.ArgumentWidths c ∧
      RamWriteFrame n q (area p) ∧ RamWriteFrame n q [⟨(p-9).toNat,9⟩] := by
  have retLow : (if secondCheck then (0x1035bf : BitVec 64) else 0x103577).toNat < 2^32 := by
    cases secondCheck <;> decide
  obtain ⟨c,comp,csp,compKeeps,cWidths,eq,binary⟩ :=
    compareReturn call win rsp di dx si cx leftRead calleeWidths df fp returnSlot retLow alignment
  obtain ⟨e,q,choice,esp,choiceKeeps,eWidths,flag,writes,small⟩ := choiceReturn secondCheck win csp binary cWidths
  have zeroIff : c[0].get 8 = 1 ↔ x = 0 := by
    rw [eq, ← zeroWords bound]
    refine ⟨fun h i hi => ?_,fun h i hi => ?_⟩
    · have zero : memLoad n (wordAddr p 64 i) 64 = 0 :=
        (rightWords i hi).trans (by simp only [Vector.getElem_replicate])
      exact (leftWords i hi).symm.trans ((h i hi).trans zero)
    · rw [leftWords i hi,rightWords i hi,h i hi,Vector.getElem_replicate]
  have isZero : e[0].get 8 = if decide (x=0) then 1 else 0 := by
    rw [flag]
    by_cases h : x=0
    · simpa only [h,decide_true,↓reduceIte] using zeroIff.mpr h
    · simpa only [h,decide_false,Bool.false_eq_true,↓reduceIte] using
        binary.resolve_right (fun one => h (zeroIff.mp one))
  obtain ⟨f,jump,fsp,testKeeps,fWidths⟩ := testZero secondCheck (decide (x=0)) isZero
  exact ⟨f,q,comp.trans (choice.trans jump),fsp.trans esp,
    fun i h => (testKeeps i h).trans ((choiceKeeps i h).trans (compKeeps i h)),
    fWidths eWidths,writes,small⟩

private theorem keepStaged {p : BitVec 64} {m n : Ram} {w : Vector (BitVec 64) 4}
    {off lower : BitVec 64} {len : Nat}
    (win : Window p m) (words : WordsAt m (p+off) 64 w)
    (writes : RamWriteFrame m n [⟨(p+lower).toNat,len⟩])
    (fit : (off-(0-9)).toNat+32 ≤ 313)
    (baseFit : (lower-(0-9)).toNat+len ≤ (off-(0-9)).toNat) :
    WordsAt n (p+off) 64 w := by
  have wordOffset : p+off-(p-9) = off-(0-9) := by bv_omega
  have baseOffset : p+lower-(p-9) = lower-(0-9) := by bv_omega
  have atWords := windowOffset win (addr := p+off) (n := 32) (by rwa [wordOffset])
  have atBase := windowOffset win (addr := p+lower) (n := len) (by rw [baseOffset]; omega)
  rw [wordOffset] at atWords
  rw [baseOffset] at atBase
  have low := win.readable.low
  apply words.of_frame writes (by decide)
  refine ⟨by change (p+off).toNat+32 ≤ 2^64; omega,fun t ht => ?_⟩
  obtain rfl := List.mem_singleton.mp ht
  exact Or.inr (by change (p+lower).toNat+len ≤ (p+off).toNat; omega)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem finish {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {st : State} {r sigS : Nat} {a : Registers} {m : Ram}
    (input : Active s d msg st true r sigS a m)
    (words : WordsAt m (sp s-216) 64 (scalarWords sigS))
    (rBound : r < domain.n) (sBound : sigS < domain.n) :
    ∃ b n, Reach (inside .l103515 a m) (core .l105d35 b n) ∧
      Constructed s d msg st r sigS b n := by
  let p := sp s-224
  have win : Window p m := by
    change Writable image m (sp s-224-9) 313
    rw [show sp s-224-9 = sp s + (0-233) by bv_omega]
    exact stackWindow call input.toMemory (by decide)
  have aligned : (p-8).toNat % 16 = 8 := by
    have stackAlign := call.stackAvailable.2.2.2
    change (stackPtr s).toNat % 16 = 8 at stackAlign
    obtain ⟨room,_,spNat⟩ := stackBounds call
    change (sp s-224-8).toNat % 16 = 8
    have base : (sp s-232).toNat = (sp s).toNat-232 := belowNat call (depth := 232) (by decide)
    rw [show sp s-224-8 = sp s-232 by bv_omega,base,spNat]
    omega
  have rWords : WordsAt m (p+64) 64 (scalarWords r) := by
    change WordsAt m (sp s-224+64) 64 (scalarWords r)
    rw [show sp s-224+64 = sp s-160 by bv_omega]
    exact input.other
  have sWords : WordsAt m (p+8) 64 (scalarWords sigS) := by
    change WordsAt m (sp s-224+8) 64 (scalarWords sigS)
    rw [show sp s-224+8 = sp s-216 by bv_omega]
    exact words
  have rbx : a[3] = ⟨64,p+232⟩ := by
    change a[3] = ⟨64,sp s-224+232⟩
    rw [show sp s-224+232 = sp s+8 by bv_omega]
    exact input.bx
  have sized (i : Fin Reg.count) (hi : i.val ∈ [3,5,8,9,12,13,14,15]) : a[i].width = 64 := by
    obtain ⟨i,h⟩ := i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width input.bx
    · exact congrArg Value.width input.bp
    · exact input.widths 8 (by decide)
    · exact input.widths 9 (by decide)
    · exact congrArg Value.width input.r12
    · exact congrArg Value.width input.r13
    · exact congrArg Value.width input.r14
    · exact congrArg Value.width input.r15
  have stay : RegionsWithin (area p) (workRegions s) := by
    obtain ⟨room,high,base⟩ := stackBounds call
    have lo : (p-9).toNat = (sp s).toNat-233 := by
      change (sp s-224-9).toNat = _
      rw [show sp s-224-9 = sp s-233 by bv_omega]
      exact belowNat call (by decide)
    have out : (p+232).toNat = (sp s).toNat+8 := by
      change (sp s-224+232).toNat = _
      rw [show sp s-224+232 = sp s+8 by bv_omega]
      exact offsetNat call (by decide)
    have bottom : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
    intro q h
    simp only [area,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;>
      refine ⟨_,List.mem_cons_self,?_⟩ <;>
      dsimp only [MemoryRegion.start,MemoryRegion.size] <;>
      rw [bottom] <;> first | (rw [lo]; omega) | (rw [out]; omega)
  have savedOutside (off : BitVec 64) (h : 192 ≤ off.toNat ∧ off.toNat ≤ 216) :
      Outside (area p) (p+off) 8 := by
    have neg : (off-(0-9)).toNat = off.toNat+9 := by
      rw [show off-(0-9) = off+9 by bv_omega, BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by change off.toNat+9 < 2^64; omega)
    have shift : p+off-(p-9) = off-(0-9) := by bv_omega
    have addr := windowOffset win (addr := p+off) (n := 8) (by rw [shift,neg]; omega)
    rw [shift,neg] at addr
    have out := windowOffset win (addr := p+232) (n := 72) (by
      rw [show p+232-(p-9) = 241 by bv_omega]; decide)
    rw [show p+232-(p-9) = 241 by bv_omega] at out
    change (p+232).toNat = (p-9).toNat+241 at out
    have low := win.readable.low
    refine ⟨by omega,fun q hq => ?_⟩
    simp only [area,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact Or.inr (by change (p-9).toNat+137 ≤ (p+off).toNat; omega)
    · exact Or.inl (by change (p+off).toNat+8 ≤ (p+232).toNat; omega)
  have finishAt {b : Registers} {n : Ram}
      (reach : Reach (inside .l103515 a m) (inside .l1035dc b n))
      (writes : RamWriteFrame m n (area p)) (rsp : b[4] = ⟨64,p⟩)
      (widths : ParseSignature.ArgumentWidths b)
      (keep : ∀ i : Fin Reg.count, i.val ∈ [5,12,13,22,39,50,51] → b[i] = a[i])
      (output : if r=0 ∨ sigS=0 then memLoad n (p+232) 8 = 1 ∧ memLoad n (p+240) 64 = 0
        else memLoad n (p+232) 8 = 0 ∧ WordsAt n (p+240) 64 (scalarWords r) ∧
          WordsAt n (p+272) 64 (scalarWords sigS)) :
      ∃ c q, Reach (inside .l103515 a m) (core .l105d35 c q) ∧ Constructed s d msg st r sigS c q := by
    have bx := (writes.memLoad_eq (savedOutside 192 (by decide))).trans
      (show memLoad m (p+192) 64 = sp s+456 by
        change memLoad m (sp s-224+192) 64 = _
        rw [show sp s-224+192 = sp s-32 by bv_omega]; exact input.savedBx)
    have r14 := (writes.memLoad_eq (savedOutside 200 (by decide))).trans
      (show memLoad m (p+200) 64 = sp s+160 by
        change memLoad m (sp s-224+200) 64 = _
        rw [show sp s-224+200 = sp s-24 by bv_omega]; exact input.constructor14)
    have r15 := (writes.memLoad_eq (savedOutside 208 (by decide))).trans
      (show memLoad m (p+208) 64 = sp s+456 by
        change memLoad m (sp s-224+208) 64 = _
        rw [show sp s-224+208 = sp s-16 by bv_omega]; exact input.constructor15)
    have tag := (writes.memLoad_eq (savedOutside 216 (by decide))).trans
      (show memLoad m (p+216) 64 = 0x105d35 by
        change memLoad m (sp s-224+216) 64 = _
        rw [show sp s-224+216 = sp s-8 by bv_omega]; exact input.constructorReturn)
    obtain ⟨c,returnRun,csp,cbx,c14,c15,retKeep,cWidths⟩ :=
      returnBlock (win.of_frame writes) rsp bx r14 r15 tag widths
    have eq (i : Fin Reg.count) (h : i.val ∈ [5,12,13,22,39,50,51]) :=
      (retKeep i h).trans (keep i h)
    have memory := input.toLoopMemory.preserve_work call ((RamWriteFrame.refl m _).trans writes stay)
    refine ⟨c,n,reach.trans returnRun,memory,?_,?_⟩
    · refine ⟨?_,(eq 22 (by decide)).trans input.df,cbx,(eq 5 (by decide)).trans input.bp,
        (eq 12 (by decide)).trans input.r12,(eq 13 (by decide)).trans input.r13,
        congrArg Value.width c14,c15,cWidths,?_⟩
      · simpa only [p,BitVec.sub_add_cancel] using csp
      · exact ⟨(congrArg Value.width (eq 39 (by decide))).trans input.fp.1,
          (congrArg Value.width (eq 50 (by decide))).trans input.fp.2.1,
          (congrArg Value.width (eq 51 (by decide))).trans input.fp.2.2⟩
    · change (if r=0 ∨ sigS=0 then _ else _) at output ⊢
      simpa only [p,reduceAddOffset] using output
  have finishFailure {b : Registers} {n : Ram}
      (reach : Reach (inside .l103515 a m) (inside .l1035cd b n))
      (writes : RamWriteFrame m n (area p)) (rsp : b[4] = ⟨64,p⟩)
      (widths : ParseSignature.ArgumentWidths b) (keep : Keeps a b) (zero : r=0 ∨ sigS=0) :
      ∃ c q, Reach (inside .l103515 a m) (core .l105d35 c q) ∧ Constructed s d msg st r sigS c q := by
    obtain ⟨c,q,write,outKeep,cWidths,frame,tag,payload⟩ :=
      writeFailure (win.of_frame writes) ((keep 3 (by decide)).trans rbx) widths
    refine finishAt (reach.trans write) (writes.trans frame (fun t ht => ⟨t,ht,Nat.le_refl _,Nat.le_refl _⟩))
      ((outKeep 4 (by decide)).trans rsp) cWidths ?_ (by rw [ite_eq_left zero]; exact ⟨tag,payload⟩)
    intro i h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    exact (outKeep i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)).trans
      (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega))
  obtain ⟨b,n,stage,bs,di,dx,si,cx,w8,w9,keep,staged,tag,zWords,copy,keepR⟩ :=
    stageS win input.rsp sWords
  have winN := win.of_frame staged
  obtain ⟨c,q,check,cs,cKeep,cWidths,choice,small⟩ := checkZero false rBound stage winN bs di dx si cx
    (winN.readable.of_offsets (show p+64 = p+64 from rfl) (addr_sub p 9) (by decide))
    (stageKeepsWidths keep w8 w9 sized) ((keep 22 (by decide)).trans input.df) (keepsFp keep input.fp)
    tag aligned (fun i hi => (keepR i hi).trans (rWords i hi)) zWords
  have total := staged.trans choice (fun t ht => ⟨t,ht,Nat.le_refl _,Nat.le_refl _⟩)
  have keepC : Keeps a c := fun i h => (cKeep i h).trans (keep i h)
  by_cases rz : r=0
  · exact finishFailure (by simpa only [rz,decide_true,checkTarget,↓reduceIte] using check)
      total cs cWidths keepC (Or.inl rz)
  have continued : Reach (inside .l103515 a m) (inside .l103585 c q) := by
    simpa only [decide_eq_false rz,checkTarget,Bool.false_eq_true,↓reduceIte] using check
  have left : WordsAt n (p+64) 64 (scalarWords r) := fun i hi => (keepR i hi).trans (rWords i hi)
  have rQ := keepStaged winN left (by simpa only [addr_sub p 9] using small) (by decide) (by decide)
  have sQ := keepStaged winN copy (by simpa only [addr_sub p 9] using small) (by decide) (by decide)
  have winQ := win.of_frame total
  obtain ⟨e,u,stage,es,di,dx,si,cx,w8,w9,keep,staged,tag,zWords,tiny⟩ := stageR winQ cs
  have rU := keepStaged winQ rQ (by simpa only [addr_sub p 8] using tiny) (by decide) (by decide)
  have sU := keepStaged winQ sQ (by simpa only [addr_sub p 8] using tiny) (by decide) (by decide)
  have winU := winQ.of_frame staged
  have eKeep : Keeps a e := fun i h => (keep i h).trans (keepC i h)
  have cSized (i : Fin Reg.count) (h : i.val ∈ [3,5,8,9,12,13,14,15]) : c[i].width = 64 := by
    by_cases args : i.val ∈ Activation.argumentNumbers
    · exact cWidths i args
    · refine (congrArg Value.width (keepC i ?_)).trans (sized i h)
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at args h ⊢
      omega
  obtain ⟨f,v,check,fs,fKeep,fWidths,choice,small⟩ := checkZero true sBound stage winU es di dx si cx
    (winU.readable.of_offsets (show p+96 = p+96 from rfl) (addr_sub p 9) (by decide))
    (stageKeepsWidths keep w8 w9 cSized) ((eKeep 22 (by decide)).trans input.df) (keepsFp eKeep input.fp)
    tag aligned sU zWords
  have writes := (total.trans staged (fun t ht => ⟨t,ht,Nat.le_refl _,Nat.le_refl _⟩)).trans choice
    (fun t ht => ⟨t,ht,Nat.le_refl _,Nat.le_refl _⟩)
  have keepF : Keeps a f := fun i h => (fKeep i h).trans (eKeep i h)
  have path := continued.trans check
  by_cases sz : sigS=0
  · exact finishFailure (by simpa only [sz,decide_true,checkTarget,↓reduceIte] using path)
      writes fs fWidths keepF (Or.inr sz)
  have path : Reach (inside .l103515 a m) (inside .l1035ec f v) := by
    simpa only [decide_eq_false sz,checkTarget,Bool.false_eq_true,↓reduceIte] using path
  have rV := keepStaged winU rU (by simpa only [addr_sub p 9] using small) (by decide) (by decide)
  have sV := keepStaged winU sU (by simpa only [addr_sub p 9] using small) (by decide) (by decide)
  obtain ⟨g,y,write,kept,gWidths,frame,tag,first,second⟩ :=
    writeSuccess (win.of_frame writes) fs ((keepF 3 (by decide)).trans rbx) rV sV
  refine finishAt (path.trans write) (writes.trans frame (fun t ht => ⟨t,ht,Nat.le_refl _,Nat.le_refl _⟩))
    ((kept 4 (by decide)).trans fs) gWidths ?_ ?_
  · intro i h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    exact (kept i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)).trans
      (keepF i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega))
  · rw [ite_eq_right (fun bad => bad.elim rz sz)]
    exact ⟨tag,first,second⟩

end K256.Proofs.Signing.Composition.Attempt.Return.Constructor
