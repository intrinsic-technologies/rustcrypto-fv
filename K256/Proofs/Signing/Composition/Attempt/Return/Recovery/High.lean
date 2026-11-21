import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.State
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Memory
import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Verify.Choice
import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Verify.LIR.Functions1
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

section VerifyExecution

open Verify.LIR (program bytes_l10a170 code_l10a170)
open Sec1.Serialize.Assemble (loadOk_memStore storeOk_memStore)

private abbrev highKept : List Nat := [3,5,9,12,13,14,15,22,39,50,51]

local macro "high_kept" : tactic => `(tactic|
  (intro ⟨i,_⟩ hi
   simp only [highKept,List.mem_cons,List.not_mem_nil,or_false] at hi
   rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl))

private theorem highRead {m : Ram} {src : BitVec 64} (r : Readable m src 32)
    (off : BitVec 64) (fit : off.toNat + 8 ≤ 32) : LoadOk m (src+off) 8 := by
  apply LoadOk.of_offsets r (x := src) (c := off) (d := 0) rfl (addr_self src)
  rw [show off - (0 : BitVec 64) = off by bv_omega]
  exact fit

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem highChoice {a : Registers} {m : Ram} {sp src : BitVec 64}
    (rsp : a[4].get 64 = sp+8) (ptr : a[7].get 64 = src)
    (read : Readable m src 32)
    (write : Writable Extracted.programImage m (sp-9) 17)
    (spRoom : 9 ≤ sp.toNat) :
    ∃ b pre, program.runBlock (dialect Extracted.programImage) ⟨.l10a170,a,m⟩ =
        .call ⟨.l127d50,b,memStore pre (sp-8) (0x10a211 : BitVec 64)⟩
          (Verify.resumeAt .l10a211 0x10a211) ∧
      b[4] = ⟨64,sp-8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,6,7,8] → b[i].width = 64) ∧
      RamWriteFrame m pre [⟨(sp-9).toNat,17⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ highKept → b[i] = a[i]) := by
  have scratch : Writable Extracted.programImage m sp 8 :=
    write.of_offsets (addr_self sp) (addr_sub sp 9) (by decide)
  have childSlot : Writable Extracted.programImage m (sp-8) 8 :=
    write.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  have base : (sp-9).toNat = sp.toNat-9 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr spRoom)
  have atSp : InRegions [⟨(sp-9).toNat,17⟩] sp 8 := by
    refine ⟨_,List.mem_singleton_self _,?_⟩
    have upper := write.readable.low
    simp only [InRegion,base] at *
    omega
  have rd0 : LoadOk m src 8 := ⟨by have := read.low; omega, fun i hi => read.present i (by omega)⟩
  have rd1 := highRead read 8 (by decide)
  have rd2 := highRead read 16 (by decide)
  have rd3 := highRead read 24 (by decide)
  have rdWord : LoadOk m sp 8 := ⟨scratch.readable.low,scratch.readable.present⟩
  have rdByte : LoadOk m sp 1 := LoadOk.of_region scratch.readable (Nat.le_refl _) (by omega)
  have guard {addr : BitVec 64} (writable : Writable Extracted.programImage m addr 8)
      (off len : Nat) (fit : off+len ≤ bytes_l10a170.length) :
      StoreOk Extracted.programImage m addr 8 (0x10a170 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange writable
      (fun x hx => Common.fnCode_subset_programImage x (code_l10a170 x hx)) fit
  have wr0 : StoreOk Extracted.programImage m sp 8 0x10a170 1 := guard scratch 0 1 (by decide)
  have wr1 : StoreOk Extracted.programImage m sp 8 0x10a188 4 := guard scratch 24 4 (by decide)
  have wr2 : StoreOk Extracted.programImage m sp 8 0x10a1b4 4 := guard scratch 68 4 (by decide)
  have wr3 : StoreOk Extracted.programImage m sp 8 0x10a1d8 4 := guard scratch 104 4 (by decide)
  have wr4 : StoreOk Extracted.programImage m sp 8 0x10a1ff 4 := guard scratch 143 4 (by decide)
  have wr5 : StoreOk Extracted.programImage m (sp-8) 8 0x10a20c 5 := guard childSlot 156 5 (by decide)
  refine ⟨?out, ?pre, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,ptr,BitVec.add_sub_cancel,rd0,rd1,rd2,rd3,rdWord,rdByte,wr0,wr1,wr2,wr3,wr4,wr5]
    refine Eq.trans (ite_eq_left (loadOk_memStore rd0)) ?_
    refine Eq.trans (ite_eq_left (storeOk_memStore wr1)) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore rdWord))) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore rd1))) ?_
    refine Eq.trans (ite_eq_left (storeOk_memStore (storeOk_memStore wr2))) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore (loadOk_memStore rdWord)))) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore (loadOk_memStore rd2)))) ?_
    refine Eq.trans (ite_eq_left (storeOk_memStore (storeOk_memStore (storeOk_memStore wr3)))) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore (loadOk_memStore (loadOk_memStore rdWord))))) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore (loadOk_memStore (loadOk_memStore rd3))))) ?_
    refine Eq.trans (ite_eq_left (storeOk_memStore (storeOk_memStore (storeOk_memStore (storeOk_memStore wr4))))) ?_
    refine Eq.trans (ite_eq_left (loadOk_memStore (loadOk_memStore (loadOk_memStore (loadOk_memStore (loadOk_memStore rdByte)))))) ?_
    refine Eq.trans (ite_eq_left (storeOk_memStore (storeOk_memStore (storeOk_memStore (storeOk_memStore (storeOk_memStore wr5)))))) ?_
    rfl
  case post =>
    refine ⟨rfl,?_,?_,by high_kept⟩
    · intro ⟨i,_⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl <;> rfl
    · iterate 5 apply RamWriteFrame.memStore _ _ atSp
      exact .refl _ _

private theorem highReturn {a : Registers} {m : Ram} {sp ret : BitVec 64}
    (rsp : a[4].get 64 = sp)
    (pop : LoadOk m sp 8) (read : LoadOk m (sp+8) 8)
    (addr : memLoad m (sp+8) 64 = ret) (small : ret.toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a211,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+16⟩ ∧
      out.values[1].width = 64 ∧ out.store = m ∧
      (∀ i : Fin Reg.count, i.val ∈ highKept ++ [2,6,7,8] → out.values[i] = a[i]) := by
  refine ⟨?_, .done ?step, ?post⟩
  case step =>
    change program.step _ _ = _
    cfg_eval [rsp,pop,read,addr,small]
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro ⟨i,_⟩ h
    simp only [highKept,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxHeartbeats 350000 in
private theorem highRun {a : Registers} {m : Ram} {sp src ret : BitVec 64}
    (rsp : a[4].get 64 = sp+8) (ptr : a[7].get 64 = src)
    (read : Readable m src 32)
    (write : Writable Extracted.programImage m (sp-9) 17)
    (retRead : Readable m (sp+8) 8) (retAt : memLoad m (sp+8) 64 = ret) (small : ret.toNat < 2^32)
    (r9 : a[9].width = 64) (spRoom : 9 ≤ sp.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a170,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+16⟩ ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨(sp-9).toNat,17⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ highKept → out.values[i] = a[i]) := by
  obtain ⟨b,pre,call,bsp,wide,wrote,keep⟩ := highChoice rsp ptr read write spRoom
  have hp := write.of_frame wrote
  have tmp : Writable Extracted.programImage pre (sp-8-1) 1 := by
    rw [show sp-8-1 = sp-9 by bv_omega]
    exact hp.sub (Nat.le_refl _) (by omega)
  have slot : Readable pre (sp-8) 8 :=
    hp.readable.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  obtain ⟨c,n,resumed,csp,_,cframe,ckeep⟩ :=
    Verify.resumeChoice call (congrArg (Value.get 64) bsp) tmp slot (by decide)
  have writeLow := write.readable.low
  have base : (sp-9).toNat = sp.toNat-9 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr spRoom)
  have next : (sp-8).toNat = sp.toNat-8 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show 8 ≤ sp.toNat by omega))
  have top : (sp+8).toNat = sp.toNat+8 := by
    rw [base] at writeLow
    rw [BitVec.toNat_add]
    change (sp.toNat + 8) % 2^64 = sp.toNat + 8
    exact Nat.mod_eq_of_lt (by omega)
  let scratch : List MemoryRegion := [⟨(sp-9).toNat,17⟩]
  have full : RamWriteFrame m n scratch := by
    refine (wrote.memStore (0x10a211 : BitVec 64) ⟨_,List.mem_singleton_self _,?_⟩).trans cframe ?_
    · change (sp-9).toNat ≤ (sp-8).toNat ∧ (sp-8).toNat+8 ≤ (sp-9).toNat+17 ∧ _
      rw [base,next]
      rw [base] at writeLow
      omega
    · intro reg hreg
      obtain rfl := List.mem_singleton.mp hreg
      rw [show sp-8-1 = sp-9 by bv_omega]
      exact ⟨_,List.mem_singleton_self _,Nat.le_refl _, by dsimp only [scratch]; omega⟩
  have returnAddr : memLoad n (sp+8) 64 = ret := by
    refine (full.memLoad_eq ?_).trans retAt
    refine ⟨by omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp-9).toNat + 17 ≤ (sp+8).toNat
    omega
  have pop := (write.readable.of_frame full).of_offsets (len := 17) (n := 8)
    (addr_self sp) (addr_sub sp 9) (by decide)
  have retSlot := retRead.of_frame full
  obtain ⟨out,run,tag,stack,o1,store,okeep⟩ :=
    highReturn (congrArg (Value.get 64) csp) ⟨pop.low,pop.present⟩ ⟨retSlot.low,retSlot.present⟩ returnAddr small
  have kept (i : Fin Reg.count) (hi : i.val ∈ highKept) : out.values[i] = a[i] := by
    refine (okeep i (List.mem_append_left _ hi)).trans ((ckeep i ?_).trans (keep i hi))
    simp only [highKept,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  refine ⟨out,Program.Exec.of_sem (resumed.exec run.sem),tag,stack,?_,store.symm ▸ full,kept⟩
  intro i hi
  have cases : i = 1 ∨ i = 9 ∨ i.val ∈ [2,6,7,8] := by
    have one : (1 : Fin Reg.count).val = 1 := rfl
    have nine : (9 : Fin Reg.count).val = 9 := rfl
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [Fin.ext_iff,one,nine,List.mem_cons,List.not_mem_nil,or_false]
    omega
  rcases cases with rfl|rfl|other
  · exact o1
  · rw [kept 9 (by decide)]
    exact r9
  · rw [okeep i (List.mem_append_right _ other),ckeep i ?_]
    · exact wide i other
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at other ⊢
      omega

private theorem highPush {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p)
    (push : StoreOk Extracted.programImage m (p-8) 8 0x105dfa 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105df2,a,m⟩ =
      .call ⟨.l10a170,b,memStore m (p-8) (0x105dff : BitVec 64)⟩ (resume .l105dff 0x105dff) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+456⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ highKept → b[i] = a[i] := by
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,push]
    rfl
  case post => exact ⟨rfl,rfl,by high_kept⟩

end VerifyExecution

theorem high {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {r sigS : Nat}
    (input : Staged s d r sigS a m) :
    ∃ b n, Reach (core .l105df2 a m) (core .l105dff b n) ∧ Staged s d r sigS b n := by
  obtain ⟨room,upper,_⟩ := stackBounds call
  have p8 : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have p16 : (sp s-16).toNat = (sp s).toNat-16 := belowNat call (by decide)
  have p25 : (sp s-25).toNat = (sp s).toNat-25 := belowNat call (by decide)
  have slot : Writable Extracted.programImage m (sp s-8) 8 := by
    rw [addr_sub]
    exact stackWindow call input.toMemory (by decide)
  have guard : StoreOk Extracted.programImage m (sp s-8) 8 0x105dfa 5 :=
    ParseSignature.storeOk_of_codeRange (off := 8) slot
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l105df2 x hx)) (by decide)
  obtain ⟨b,step,bsp,bdi,keep⟩ := highPush (congrArg (Value.get 64) input.rsp) guard
  let t := memStore m (sp s-8) (0x105dff : BitVec 64)
  have write : Writable Extracted.programImage t (sp s-25) 17 := by
    have wt : Writable Extracted.programImage m (sp s-25) 17 := by
      rw [addr_sub]
      exact stackWindow call input.toMemory (by decide)
    exact wt.memStore _ _
  have read : Readable t (sp s+456) 32 :=
    (stackWindow call input.toMemory (offset := 456) (size := 32) (by decide)).readable.memStore _ _
  have retRead : Readable t (sp s-8) 8 := slot.readable.memStore _ _
  have ret : memLoad t (sp s-8) 64 = 0x105dff :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have r9 : b[9].width = 64 :=
    (congrArg Value.width (keep 9 (by decide))).trans (input.args 9 (by decide))
  have a8 : sp s-16+8 = sp s-8 := by bv_omega
  have a16 : sp s-16+16 = sp s := by bv_omega
  have a25 : sp s-16-9 = sp s-25 := by bv_omega
  obtain ⟨out,run,tag,stack,args,writes,kept⟩ := highRun (sp := sp s-16) (ret := 0x105dff)
    (by rw [a8]; exact congrArg (Value.get 64) bsp) (congrArg (Value.get 64) bdi)
    read (by rwa [a25]) (by rwa [a8]) (by rwa [a8])
    (by decide) r9 (by rw [p16]; omega)
  let footprint : List MemoryRegion := [⟨(sp s-25).toNat,25⟩]
  have pushed : RamWriteFrame m t footprint :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_,List.mem_singleton_self _,
      by simp only [InRegion,Nat.reduceDiv,p8,p25]; omega⟩
  have frame : RamWriteFrame m out.store footprint := by
    apply pushed.trans writes
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨_,List.mem_singleton_self _,by simp only [a25]; omega⟩
  have memory := preserveCore call input.toCoreMemory frame (by
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    change _ ≤ (sp s-25).toNat ∧ (sp s-25).toNat+25 ≤ _
    omega)
  have outside (o : Nat) (ho : o ≤ 224) : Outside footprint (sp s+BitVec.ofNat 64 o) 32 := by
    simp only [footprint, Outside, offsetNat call (by omega : o ≤ 1296), p25,
      List.mem_singleton,forall_eq]
    exact ⟨by omega,Or.inr (by omega)⟩
  have same (i : Fin Reg.count) (hi : i.val ∈ highKept) : out.values[i] = a[i] :=
    (kept i hi).trans (keep i hi)
  have saved (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      out.values[i].width = 64 := by
    rw [same i ?_]
    · exact input.saved i hi
    · simp only [Activation.calleeSavedNumbers,highKept,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
  have reach := callReaches step (Signing.Transfer.verifyExecAt rfl run) tag
  rw [a16] at stack
  exact ⟨_,_,reach,memory,stack,(same 22 (by decide)).trans input.df,saved,args,
    ⟨(congrArg Value.width (same 39 (by decide))).trans input.fp.1,
     (congrArg Value.width (same 50 (by decide))).trans input.fp.2.1,
     (congrArg Value.width (same 51 (by decide))).trans input.fp.2.2⟩,
    input.first.of_frame frame (by decide) (outside 192 (by decide)),
    input.second.of_frame frame (by decide) (outside 224 (by decide))⟩

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
