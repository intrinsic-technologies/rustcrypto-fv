import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.State
import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Verify.Transfer.Signature.Relabel
import K256.Proofs.ParseSignature.Scalar
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Return.Constructor

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Signing.LIR

private abbrev decodeSite (second : Bool) : Label := if second then .l1034fb else .l103472
private abbrev branchSite (second : Bool) : Label := if second then .l10350b else .l103482
private abbrev successSite (second : Bool) : Label := if second then .l103515 else .l10348c
private abbrev returnAddr (second : Bool) : BitVec 64 := if second then 0x10350b else 0x103482
private abbrev source (p : BitVec 64) (second : Bool) : BitVec 64 :=
  if second then p-64 else p-96

set_option maxHeartbeats 500000 in
private theorem callBlock {a : Registers} {m : Ram} {p : BitVec 64} (second : Bool)
    (rsp : a[4].get 64 = p-224)
    (rsi : (if second then a[14] else a[15]).get 64 = source p second)
    (win : Writable Extracted.programImage m (p-232) 8) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨decodeSite second,a,m⟩ =
        .call ⟨.l107730,b,memStore m (p-232) (returnAddr second)⟩
          (resume (branchSite second) (returnAddr second)) ∧
      b[4] = ⟨64,p-232⟩ ∧ b[2] = ⟨64,32⟩ ∧
      b[6] = ⟨64,source p second⟩ ∧ b[7] = ⟨64,p-224⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have addr : p-224-8 = p-232 := by bv_omega
  cases second
  case false =>
    change a[15].get 64 = p-96 at rsi
    refine ⟨?bFirst,?runFirst,?regsFirst⟩
    case runFirst =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l103472,a,m⟩ =
        .call ⟨.l107730,_,memStore m (p-232) (0x103482 : BitVec 64)⟩ (resume .l103482 0x103482)
      cfg_eval [rsp,rsi,addr]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l103472)
      rfl
    case regsFirst =>
      refine ⟨rfl,rfl,rfl,rfl,?_⟩
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case true =>
    change a[14].get 64 = p-64 at rsi
    refine ⟨?bSecond,?runSecond,?regsSecond⟩
    case runSecond =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l1034fb,a,m⟩ =
        .call ⟨.l107730,_,memStore m (p-232) (0x10350b : BitVec 64)⟩ (resume .l10350b 0x10350b)
      cfg_eval [rsp,rsi,addr]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1034fb)
      rfl
    case regsSecond =>
      refine ⟨rfl,rfl,rfl,rfl,?_⟩
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxHeartbeats 500000 in
private theorem branchBlock {a : Registers} {m : Ram} {p : BitVec 64} (second : Bool)
    (rsp : a[4] = ⟨64,p-224⟩) (rd : LoadOk m (p-224) 4)
    (valid : memLoad m (p-224) 64 = 0) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨branchSite second,a,m⟩ =
        .jump ⟨successSite second,b,m⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] →
        b[i] = a[i]) := by
  have rs : a[4].get 64 = p-224 := by rw [rsp]; rfl
  have low : memLoad m (p-224) 32 = 0 := by
    have h := extractLsb'_memLoad m (p-224) (n := 64) 0 32 (by decide) (by decide) (by decide)
    rw [valid, Nat.zero_div, BitVec.add_zero] at h
    exact h.symm
  cases second
  case false =>
    refine ⟨?bFirst,?runFirst,?regsFirst⟩
    case runFirst =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l103482,a,m⟩ =
        .jump ⟨.l10348c,_,m⟩
      cfg_eval [rs,rd,low]
      simp only [cmpSpec_ZF]
      rfl
    case regsFirst =>
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case true =>
    refine ⟨?bSecond,?runSecond,?regsSecond⟩
    case runSecond =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l10350b,a,m⟩ =
        .jump ⟨.l103515,_,m⟩
      cfg_eval [rs,rd,low]
      simp only [cmpSpec_ZF]
      rfl
    case regsSecond =>
      intro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private abbrev decodeWrites (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-600).toNat,416⟩]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem decode {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {st : State} {r sigS : Nat} {a : Registers} {m : Ram}
    {second : Bool} (input : Active s d msg st second r sigS a m)
    (bytes : encoded s second m (if second then sigS else r))
    (bound : (if second then sigS else r) < domain.n) :
    ∃ b n, Reach (inside (if second then .l1034fb else .l103472) a m)
      (inside (if second then .l103515 else .l10348c) b n) ∧
      Active s d msg st second r sigS b n ∧
      WordsAt n (sp s-216) 64 (scalarWords (if second then sigS else r)) := by
  let p := sp s
  let ret := returnAddr second
  let start := memStore m (p-232) ret
  obtain ⟨room, limit, base⟩ := stackBounds call
  change p.toNat = _ at base
  have below (i : Nat) (hi : i ≤ 9904) : (p-BitVec.ofNat 64 i).toNat = p.toNat-i :=
    belowNat call hi
  have lower : (p-600).toNat = p.toNat-600 := below 600 (by decide)
  have slot : (p-232).toNat = p.toNat-232 := below 232 (by decide)
  have dest : (p-224).toNat = p.toNat-224 := below 224 (by decide)
  have workLo : (p-9904).toNat = p.toNat-9904 := below 9904 (by decide)
  have otherFirst : (p+456).toNat = p.toNat+456 := offsetNat call (by decide)
  have otherSecond : (p-160).toNat = p.toNat-160 := below 160 (by decide)
  have src : (source p second).toNat = p.toNat-(if second then 64 else 96) := by
    cases second
    · exact below 96 (by decide)
    · exact below 64 (by decide)
  have window {i size : Nat} (hi : i ≤ 9904) (hs : size ≤ i) :
      Writable Extracted.programImage m (p-BitVec.ofNat 64 i) size := by
    rw [addr_sub]
    apply stackWindow call input.toMemory
    have iv : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    have n : ((9904 : BitVec 64) - BitVec.ofNat 64 i).toNat = 9904-i := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,iv]; exact hi),iv]
      rfl
    rw [show 0 - BitVec.ofNat 64 i + 9904 = (9904 : BitVec 64) - BitVec.ofNat 64 i by bv_omega, n]
    omega
  have sourceReg : (if second then a[14] else a[15]).get 64 = source p second := by
    cases second
    · change a[15].get 64 = p-96
      rw [input.r15]; rfl
    · change a[14].get 64 = p-64
      rw [input.r14]; rfl
  obtain ⟨args,run,rsp,dx,si,di,keep⟩ :=
    callBlock second (congrArg (Value.get 64) input.rsp) sourceReg
      (window (i:=232) (by decide) (by decide))
  let fr : Activation := ParseSignature.withArguments
    { original := start
      rsp := p-232
      low := p-600
      ret := ret
      rbx := a[3].get 64
      rbp := a[5].get 64
      r12 := a[12].get 64
      r13 := a[13].get 64
      r14 := a[14].get 64
      r15 := a[15].get 64
      mxcsr := a[39].get 32
      ftw := a[50].get 16
      fcw := a[51].get 16
      fs := s.FS
      rdi := 0
      rsi := 0
      rdx := 0
      rcx := 0
      r8 := 0
      r9 := 0 } args
  have frdx : fr.rdx = 32 := congrArg (Value.get 64) dx
  have frsi : fr.rsi = source p second := congrArg (Value.get 64) si
  have frdi : fr.rdi = p-224 := congrArg (Value.get 64) di
  have small : ret.toNat < 2^32 := by cases second <;> decide
  have slotWritten : InRegions (decodeWrites p) (p-232) 8 := by
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change (p-600).toNat ≤ (p-232).toNat ∧
      (p-232).toNat+8 ≤ (p-600).toNat+416 ∧ (p-232).toNat+8 ≤ 2^64
    rw [lower,slot]
    omega
  have pre : RamWriteFrame m start (decodeWrites p) :=
    (RamWriteFrame.refl m _).memStore ret slotWritten
  have within : RegionsWithin (decodeWrites p) (workRegions s) := by
    intro reg h
    obtain rfl := List.mem_singleton.mp h
    refine ⟨_,List.mem_cons_self,?_⟩
    change (p-9904).toNat ≤ (p-600).toNat ∧ (p-600).toNat+416 ≤ (p-9904).toNat+10248
    rw [lower,workLo]
    omega
  have stable := input.toLoopMemory.preserve_work call ((RamWriteFrame.refl m _).trans pre within)
  have sourceOutside {rs : List MemoryRegion} (h : ∀ reg ∈ rs, reg.start + reg.size ≤ p.toNat-184) :
      Outside rs (source p second) 32 := by
    refine ⟨?_,fun reg hr => Or.inr ?_⟩ <;> rw [src]
    · split <;> omega
    · have := h reg hr
      split <;> omega
  have srcBefore : Readable m (source p second) 32 := by
    cases second
    · exact (window (i:=96) (by decide) (by decide)).readable
    · exact (window (i:=64) (by decide) (by decide)).readable
  have srcAfter : Readable start fr.rsi 32 := frsi.symm ▸ srcBefore.of_frame pre
  have dstAfter : Writable Extracted.programImage start fr.rdi 40 :=
    frdi.symm ▸ (window (i:=224) (by decide) (by decide)).of_frame pre
  have outside {addr : BitVec 64} {n : Nat}
      (lo : p.toNat-224 ≤ addr.toNat) (hi : addr.toNat+n ≤ 2^64) :
      Outside [ParseSignature.callStack fr] addr n := by
    refine ⟨hi,fun reg h => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp h
    change (p-600).toNat + ((p-232).toNat + 8 - (p-600).toNat) ≤ addr.toNat
    omega
  have argsWidth : ParseSignature.ArgumentWidths args := by
    intro ⟨i,hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg Value.width dx
      | exact congrArg Value.width si
      | exact congrArg Value.width di
      | exact (congrArg Value.width (keep _ (by decide +revert))).trans (input.widths _ (by decide +revert))
  have rbx := (keep 3 (by decide)).trans (value_eq (congrArg Value.width input.bx))
  have rbp := (keep 5 (by decide)).trans (value_eq (congrArg Value.width input.bp))
  have r12 := (keep 12 (by decide)).trans (value_eq (congrArg Value.width input.r12))
  have r13 := (keep 13 (by decide)).trans (value_eq (congrArg Value.width input.r13))
  have r14 := (keep 14 (by decide)).trans (value_eq (congrArg Value.width input.r14))
  have r15 := (keep 15 (by decide)).trans (value_eq (congrArg Value.width input.r15))
  have mx := (keep 39 (by decide)).trans (value_eq input.fp.1)
  have ft := (keep 50 (by decide)).trans (value_eq input.fp.2.1)
  have fc := (keep 51 (by decide)).trans (value_eq input.fp.2.2)
  have ro : Proofs.LIR.rodataSection ∈ Extracted.programSections := .tail _ (.head _)
  have slots := Proofs.LIR.Fn107730.callSlots_loaded ro (stable.toMemory.image call)
  obtain ⟨rr1,v1⟩ := slots (0x203dd0,0x12a820) (by decide)
  obtain ⟨rr2,v2⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨rr3,v3⟩ := slots (0x203e20,0x100a20) (by decide)
  have span := Proofs.LIR.Fn107730.callSlots_span ro
  have avoids := (call.separation.2 _ (show Stack.region s signingKeyTrySign.minStackBytes ∈
      writtenRegions signingKeyTrySign s by simp [writtenRegions])).1
  have separate := apart_of_avoids (lo:=0x203dd0) (hi:=0x203e28) avoids
    (fun addr lo hi => by
      obtain ⟨b,hb⟩ := span addr lo hi
      exact Or.inl ⟨b,Common.programSections_fetchByte_of_mem hb⟩)
    (by rw [stackRegion call]; exact (by decide : 0 < 11200)) (by decide) (by decide)
  rw [stackRegion call] at separate
  change (stackPtr s - 11192#64).toNat + 11200 ≤ 0x203dd0 ∨
    0x203e28 ≤ (stackPtr s - 11192#64).toNat at separate
  rw [Common.stackOffset (off:=11192) call.stackAvailable (by decide)] at separate
  have align := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at align
  have entry : Atom.All Extracted.programImage args start (Proofs.LIR.Fn107730.frameInfo.entryAtoms fr) := by
    change Atom.All Extracted.programImage args start (Proofs.LIR.Fn107730.frameAt .l107730 fr)
    simp only [Proofs.LIR.Fn107730.frameAt,Proofs.LIR.Fn107730.frameAtG0,Atom.All,Atom.Holds]
    refine ⟨rsp,(keep 22 (by decide)).trans input.df,ParseSignature.entryArgument argsWidth _ 1 (by decide),
      dx.trans (congrArg (Value.mk 64) frdx.symm),rbx,rbp,
      si.trans (congrArg (Value.mk 64) frsi.symm),di.trans (congrArg (Value.mk 64) frdi.symm),
      ParseSignature.entryArgument argsWidth _ 8 (by decide),
      ParseSignature.entryArgument argsWidth _ 9 (by decide),
      r12,r13,r14,r15,mx,ft,fc,?_,?_,small,?_,?_,?_,rr1,v1,rr2,v2,rr3,v3,?_,trivial⟩
    · exact ((window (i:=232) (by decide) (by decide)).of_frame pre).readable
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · change Writable Extracted.programImage start (p-232-368) 368
      rw [show p-232-368 = p-600 by bv_omega]
      exact (window (i:=600) (by decide) (by decide)).of_frame pre
    · change (p-600).toNat + 368 ≤ (p-232).toNat
      omega
    · change (p-232).toNat % 16 = 8
      omega
    · change 0x203f98 ≤ (p-232).toNat ∨ (p-232).toNat ≤ 0x203dd0
      omega
  obtain ⟨parsed,exec,tag,done_,writes,widths,post⟩ :=
    ParseSignature.decode_call Common.fnCode_subset_programImage fr frdx srcAfter dstAfter
      (outside (by rw [frsi,src]; split <;> omega) (by rw [frsi,src]; split <;> omega))
      (outside (by rw [frdi,dest]; exact Nat.le_refl _) (by rw [frdi,dest]; omega)) args entry
  have srcOld := sourceOutside (rs:=decodeWrites p) (by
    intro reg h
    obtain rfl := List.mem_singleton.mp h
    change (p-600).toNat + 416 ≤ p.toNat-184
    omega)
  have encodedStart (i : Nat) (hi : i < 4) :
      Common.scalarWord start fr.rsi i = (scalarWords (if second then sigS else r))[i] := by
    rw [frsi]
    refine Eq.trans ?_ (bytes i hi)
    unfold Common.scalarWord
    congr 1
    apply pre.memLoad_eq
    have hOff : 8 * (3 - i) ≤ 24 := by omega
    have hAddr : (source p second + BitVec.ofNat 64 (8*(3-i))).toNat =
        (source p second).toNat + 8*(3-i) := by
      have off : (BitVec.ofNat 64 (8*(3-i))).toNat = 8*(3-i) :=
        Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, off]
      exact Nat.mod_eq_of_lt (by have := srcOld.1; omega)
    refine ⟨by rw [hAddr]; have := srcOld.1; omega,fun reg hr => ?_⟩
    have h := srcOld.2 reg hr
    rw [hAddr]
    rcases h with h|h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have decoded : ParseSignature.scalarValue start fr.rsi = (if second then sigS else r) := by
    generalize eq : (if second then sigS else r) = x at encodedStart bound ⊢
    calc
      _ = Generate.Generator.Multiply.Split.scalarValue (scalarWords x) := by
        simp only [ParseSignature.scalarValue,encodedStart 0 (by decide),encodedStart 1 (by decide),
          encodedStart 2 (by decide),encodedStart 3 (by decide),Generate.Generator.Multiply.Split.scalarValue,
          Nat.reducePow]
        change _ = (scalarWords x)[0].toNat + 2^64 * ((scalarWords x)[1].toNat +
          2^64 * ((scalarWords x)[2].toNat + 2^64 * (scalarWords x)[3].toNat))
        omega
      _ = x := Generate.Generator.Multiply.Split.scalarWords_value x (Nat.lt_trans bound (by decide +kernel))
  dsimp only at post
  change (if ParseSignature.scalarValue start fr.rsi < domain.n then
    memLoad parsed.store fr.rdi 64 = 0 ∧ ParseSignature.scalarLimbsAt parsed.store (fr.rdi+8) start fr.rsi
    else memLoad parsed.store fr.rdi 64 = 1) at post
  rw [decoded,ite_eq_left bound] at post
  have parsedWords : WordsAt parsed.store (p-216) 64 (scalarWords (if second then sigS else r)) := by
    intro i hi
    rw [← encodedStart i hi, ← post.2 i hi, frdi, show p-224+8 = p-216 by bv_omega]
  have combined : RamWriteFrame m parsed.store (decodeWrites p) := by
    apply pre.trans writes
    intro reg hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · change (p-600).toNat ≤ (p-600).toNat ∧
        (p-600).toNat + ((p-232).toNat-(p-600).toNat) ≤ (p-600).toNat+416
      omega
    · change (p-600).toNat ≤ fr.rdi.toNat ∧ fr.rdi.toNat+40 ≤ (p-600).toNat+416
      rw [frdi,dest]
      omega
  obtain ⟨out,vrun,memEq,tagEq,regsEq⟩ :=
    Verify.Transfer.Signature.transferAt (y:=Verify.LIR.Label.l107730) rfl exec
  have transferred := Transfer.verifyExecAt (dst:=Label.l107730) rfl vrun
  have resumeReach : Reach (inside (decodeSite second) a m)
      (inside (branchSite second) out.values out.store) := by
    let frame := resume (branchSite second) ret
    refine .step (b:=⟨⟨.l107730,args,start⟩,frame::[
      resume .l105d35 0x105d35,resume .l102795 0x102795]⟩) ?_ ?_
    · exact congrArg (Transfer.next (dialect Extracted.programImage)
        [resume .l105d35 0x105d35,resume .l102795 0x102795]) run
    · exact ParseSignature.exec_reaches_resume transferred frame _
        (by
          dsimp only [frame]
          rw [tagEq,tag]
          exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))
  change Atom.All _ _ _ (Proofs.LIR.Fn107730.doneAt fr) at done_
  simp only [Proofs.LIR.Fn107730.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨rsp',df',bx',bp',r12',r13',r14',r15',mx',ft',fc',_⟩ := done_
  have afterRsp : out.values[4] = ⟨64,p-224⟩ := by
    exact (regsEq 4 (by decide)).trans (rsp'.trans
      (congrArg (Value.mk 64) (show p-232+8 = p-224 by bv_omega)))
  have readTag : LoadOk out.store (p-224) 4 := by
    rw [memEq]
    exact LoadOk.of_region (dstAfter.of_frame writes).readable
      (by rw [frdi]; exact Nat.le_refl _) (by rw [frdi]; omega)
  obtain ⟨b,jump,afterRegs⟩ := branchBlock second afterRsp readTag (by rw [memEq,← frdi]; exact post.1)
  have finalRegs (i : Fin Reg.count) (hi : i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51]) :
      b[i] = parsed.values[i] := by
    exact (afterRegs i hi).trans (regsEq i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega))
  have afterMemory : RamWriteFrame m out.store (decodeWrites p) := memEq ▸ combined
  have outsideAfter {addr : BitVec 64} {len : Nat}
      (lo : p.toNat-184 ≤ addr.toNat) (hi : addr.toNat+len ≤ 2^64) :
      Outside (decodeWrites p) addr len := by
    refine ⟨hi,fun reg hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (p-600).toNat+416 ≤ addr.toNat
    omega
  have saved {off : Nat} (h : off ≤ 32) :
      memLoad out.store (p-BitVec.ofNat 64 off) 64 =
        memLoad m (p-BitVec.ofNat 64 off) 64 := by
    apply afterMemory.memLoad_eq
    apply outsideAfter <;> rw [below off (by omega)] <;> omega
  have other := input.other
  have otherAfter : if second then WordsAt out.store (p-160) 64 (scalarWords r)
      else WordsAt out.store (p+456) 64 (scalarWords sigS) := by
    cases second
    · change WordsAt m (p+456) 64 (scalarWords sigS) at other
      apply other.of_frame afterMemory (by decide)
      apply outsideAfter <;> rw [otherFirst] <;> omega
    · change WordsAt m (p-160) 64 (scalarWords r) at other
      apply other.of_frame afterMemory (by decide)
      apply outsideAfter <;> rw [otherSecond] <;> omega
  refine ⟨b,out.store,resumeReach.trans (.single ?_),?_,memEq ▸ parsedWords⟩
  · exact congrArg (Transfer.next (dialect Extracted.programImage)
      [resume .l105d35 0x105d35,resume .l102795 0x102795]) jump
  refine ⟨input.toLoopMemory.preserve_work call ((RamWriteFrame.refl m _).trans afterMemory within),
    (afterRegs 4 (by decide)).trans afterRsp,(finalRegs 22 (by decide)).trans df',
    ?_,?_,?_,?_,?_,?_,?_,?_,(saved (off:=32) (by decide)).trans input.savedBx,
    (saved (off:=24) (by decide)).trans input.constructor14,
    (saved (off:=16) (by decide)).trans input.constructor15,
    (saved (off:=8) (by decide)).trans input.constructorReturn,otherAfter⟩
  · exact (finalRegs 3 (by decide)).trans (bx'.trans (congrArg (fun v => Value.mk 64 (v.get 64)) input.bx))
  · exact (finalRegs 5 (by decide)).trans (bp'.trans (congrArg (fun v => Value.mk 64 (v.get 64)) input.bp))
  · exact (finalRegs 12 (by decide)).trans (r12'.trans (congrArg (fun v => Value.mk 64 (v.get 64)) input.r12))
  · exact (finalRegs 13 (by decide)).trans (r13'.trans (congrArg (fun v => Value.mk 64 (v.get 64)) input.r13))
  · exact (finalRegs 14 (by decide)).trans (r14'.trans (congrArg (fun v => Value.mk 64 (v.get 64)) input.r14))
  · exact (finalRegs 15 (by decide)).trans (r15'.trans (congrArg (fun v => Value.mk 64 (v.get 64)) input.r15))
  · intro i hi
    rw [finalRegs i (by
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)]
    exact widths i hi
  · exact ⟨congrArg Value.width ((finalRegs 39 (by decide)).trans mx'),
      congrArg Value.width ((finalRegs 50 (by decide)).trans ft'),
      congrArg Value.width ((finalRegs 51 (by decide)).trans fc')⟩

end K256.Proofs.Signing.Composition.Attempt.Return.Constructor
