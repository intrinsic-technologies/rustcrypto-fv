import AesGcm.Proofs.Machine.Core.Decrypt.Calls
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.Runtime.MemorySlices

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 800000 in
theorem copy_exec (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (ret : BitVec 64)
    (source destination : BitVec 64) (input : ByteArray)
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1,0⟩)
    (h39 : args[39] = ⟨32,args[39].get 32⟩)
    (h50 : args[50] = ⟨16,args[50].get 16⟩)
    (h51 : args[51] = ⟨16,args[51].get 16⟩)
    (hsource : args[6].get 64 = source) (hdest : args[7].get 64 = destination)
    (hcount : (args[2].get 64).toNat = input.size)
    (hstack : Readable mem (args[4].get 64) 8)
    (hret : memLoad mem (args[4].get 64) 64 = ret) (hretLow : ret.toNat < 2^32)
    (halign : (args[4].get 64).toNat % 16 = 8)
    (hr : Readable mem source input.size) (hw : Writable code mem destination input.size)
    (hb : (span source input.size).HasBytes mem input)
    (hsep : source.toNat + input.size ≤ destination.toNat ∨
      destination.toNat + input.size ≤ source.toNat)
    (hreturnSep : RangeApart destination input.size (args[4].get 64) 8) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨⟨.l103f00,args,mem⟩,[]⟩ output ∧
      output.tag = some ⟨64,ret⟩ ∧ GPRsTyped output.values ∧
      output.values[4] = ⟨64,args[4].get 64 + 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → output.values[r] = args[r]) ∧
      RamWriteFrame mem output.store [span (args[4].get 64) 8,span destination input.size] ∧
      (span destination input.size).HasBytes output.store input := by
  let af := activationOfValues mem args ret (args[4].get 64)
  have hp : memcpyPre code af mem := by
    dsimp only [memcpyPre,af,activationOfValues]
    simpa only [hsource,hdest,hcount] using And.intro hr (And.intro hw (And.intro hsep hreturnSep))
  obtain ⟨output,exec,tag,done,typed,frame,bytes⟩ := callContract_exec_values
    LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
    (fun fr ↦ [span fr.rdi fr.rdx.toNat]) _ _
    (memcpy_call code (fun x hx ↦ hcode x (LIR.code_l103f00 x hx)))
    mem args ret (args[4].get 64) hTypes h39 h50 h51 hdf hstack hret hretLow
    (by intro h; contradiction) (by change _ + 0 ≤ _; omega) halign (by trivial) hp
  change Atom.All code output.values output.store (LIR.Fn103f00.frameInfo.doneAtoms af) at done
  rcases done with ⟨o4,o22,o3,o5,o12,o13,o14,o15,o39,o50,o51,_⟩
  have keep (r : Fin 53) (hin : r.val ∈ [3,5,12,13,14,15,22,39,50,51]) : output.values[r] = args[r] := by
    rcases r with ⟨r,hrlt⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact o3.trans (hTypes.value 3).symm
    · exact o5.trans (hTypes.value 5).symm
    · exact o12.trans (hTypes.value 12).symm
    · exact o13.trans (hTypes.value 13).symm
    · exact o14.trans (hTypes.value 14).symm
    · exact o15.trans (hTypes.value 15).symm
    · exact o22.trans hdf.symm
    · exact o39.trans h39.symm
    · exact o50.trans h50.symm
    · exact o51.trans h51.symm
  refine ⟨output,exec,tag,typed,o4,keep,?_,?_⟩
  · change RamWriteFrame mem output.store [af.region,span af.rdi af.rdx.toNat] at frame
    apply (RamWriteFrame.refl _ _).trans frame
    intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span (args[4].get 64) 8,by simp,?_,?_⟩ <;>
        simp only [Activation.region,activationOfValues,af,span] <;> omega
    · exact ⟨span destination input.size,by simp,
        by change destination.toNat ≤ (args[7].get 64).toNat; rw [hdest]; exact Nat.le_refl _,
        by change (args[7].get 64).toNat + (args[2].get 64).toNat ≤ destination.toNat + input.size; rw [hdest,hcount]; exact Nat.le_refl _⟩
  · apply hasBytes_of_copy hb
    simpa only [activationOfValues,hsource,hdest,hcount] using bytes


set_option maxHeartbeats 1200000 in
theorem copyTailIn_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp source : BitVec 64) (input : ByteArray)
    (hsp : args[4].get 64 = sp) (hsource : args[13].get 64 = source)
    (hcount : (args[14].get 64).toNat = input.size) (hsize : input.size ≤ 16)
    (hpositive : 0 < input.size) (hroom : 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - 8) 176) (hr : Readable mem source input.size)
    (hb : (span source input.size).HasBytes mem input)
    (hsep : (span (sp - 8) 176).Disjoint (span source input.size))
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1,0⟩)
    (h39 : args[39] = ⟨32,args[39].get 32⟩)
    (h50 : args[50] = ⟨16,args[50].get 16⟩)
    (h51 : args[51] = ⟨16,args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l10290b else .l1024ab,args,mem⟩,[]⟩ ⟨next,[]⟩ ∧
      next.label = (if use256 then .l102926 else .l1024c6) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,5,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (next.arguments[3]'(by change 3 < 53; decide)).get 64 = sp + 152 ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = 0x103f00 ∧
      RamWriteFrame mem next.store [span (sp - 8) 8,span (sp + 152) input.size] ∧
      (span (sp + 152) input.size).HasBytes next.store input := by
  have ns : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hroom)
  have low : sp.toNat + 168 ≤ 2^32 := by have hh := hw.readable.low; rw [ns] at hh; omega
  have nd : (sp + 152).toNat = sp.toNat + 152 := by bv_omega
  have ap := disjoint_bounds _ _ _ _ (by decide : 0 < 176) hpositive hsep
  rw [ns] at ap
  obtain ⟨callee,cont,run,label,target,guard,memory,c4,c7,c6,c2,c3,c12,keep,typed⟩ :=
    tail_copy_in_runBlock use256 code hcode args mem (by rw [hsp]; exact hw.sub (Nat.le_refl _) (by omega))
  have hf : RamWriteFrame mem callee.store [span (sp - 8) 8] := by
    rw [memory,hsp]
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨span (sp - 8) 8,by simp,?_⟩
    simp only [InRegion,span,ns]
    omega
  have bytes : (span source input.size).HasBytes callee.store input :=
    hasBytes_of_frame hf hb (Nat.le_trans hr.low (by decide)) (by
      intro r hin x hx hy
      obtain rfl := List.mem_singleton.mp hin
      exact hsep x (by simp only [span,MemoryRegion.Contains,ns] at hy ⊢; omega) hx)
  have sp' : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [c4,hsp]; rfl
  have src' : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = source := by rw [c6,hsource]; rfl
  have dst' : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 152 := by rw [c7,hsp]; rfl
  have count' : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = input.size := by rw [c2]; exact hcount
  have fp39 : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32,args[39].get 32⟩ := (keep 39 (by decide)).trans h39
  have fp50 : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16,args[50].get 16⟩ := (keep 50 (by decide)).trans h50
  have fp51 : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16,args[51].get 16⟩ := (keep 51 (by decide)).trans h51
  obtain ⟨output,exec,tag,ot,o4,ok,oframe,obytes⟩ := copy_exec code hcode callee.arguments callee.store
    (if use256 then 0x102926 else 0x1024c6) source (sp + 152) input
    (typed hTypes) ((keep 22 (by decide)).trans hdf)
    (by rw [fp39]; rfl) (by rw [fp50]; rfl)
    (by rw [fp51]; rfl) src' dst' count'
    (by rw [sp']; exact (hw.readable.of_frame hf).sub (Nat.le_refl _) (by omega))
    (by rw [sp',memory,hsp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
    (by cases use256 <;> decide) (by rw [sp',ns]; omega) (hr.of_frame hf)
    (by apply (hw.of_frame hf).sub <;> rw [ns,nd] <;> omega) bytes
    (by rw [nd]; omega)
    (by apply RangeApart.of_toNat <;> simp only [sp',ns,nd] <;> omega)
  let next := cont.resume output
  have na : next.arguments = output.values := CFGCall.resume_arguments cont output
  have ex : LIR.program.Exec (dialect code) ⟨callee,[]⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label,callee.arguments,callee.store⟩,[]⟩ output
    rw [label]; exact exec
  have accept : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts,guard,tag]
    cases use256 <;> rfl
  have step : LIR.program.step (dialect code)
      ⟨⟨if use256 then .l10290b else .l1024ab,args,mem⟩,[]⟩ = .next ⟨callee,[cont]⟩ := by
    rw [Program.step,run]; rfl
  refine ⟨next,(Semantics.Reaches.single step).trans (CFGCall.exec_reaches_resume ex cont [] accept),
    by exact target,by simpa only [na] using ot,?_,?_,?_,?_,obytes⟩
  · intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h
    · have r4 : r = 4 := Fin.ext h
      subst r
      rw [na]
      change output.values[4] = args[4]
      apply o4.trans
      rw [sp',show sp - 8 + 8 = sp by bv_omega]
      exact (congrArg (Value.mk 64) hsp.symm).trans (hTypes.value 4).symm
    all_goals rw [na]
    all_goals exact (ok r (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)).trans (keep r (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega))
  · rw [na]
    exact (congrArg (Value.get 64) (ok 3 (by decide))).trans
      ((congrArg (Value.get 64) c3).trans (congrArg (fun x : BitVec 64 ↦ x + 152) hsp))
  · rw [na]
    exact (congrArg (Value.get 64) (ok 12 (by decide))).trans (congrArg (Value.get 64) c12)
  · have before : RamWriteFrame mem callee.store [span (sp - 8) 8,span (sp + 152) input.size] := by
      apply (RamWriteFrame.refl _ _).trans hf
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      exact ⟨span (sp - 8) 8,by simp,Nat.le_refl _,Nat.le_refl _⟩
    change RamWriteFrame mem output.store _
    have after : RamWriteFrame callee.store output.store [span (sp - 8) 8,span (sp + 152) input.size] := by
      simpa only [sp'] using oframe
    exact before.trans after (fun r hin ↦ ⟨r,hin,Nat.le_refl _,Nat.le_refl _⟩)



set_option maxHeartbeats 1200000 in
theorem copyTailOut_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp descriptor destination : BitVec 64) (input : ByteArray)
    (hsp : args[4].get 64 = sp) (hsource : args[3].get 64 = sp + 152)
    (htarget : args[12].get 64 = 0x103f00)
    (hcount : (args[14].get 64).toNat = input.size) (hsize : input.size ≤ 16)
    (hpositive : 0 < input.size) (hroom : 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - 8) 176)
    (hrdesc : Readable mem descriptor 24)
    (hdescriptor : memLoad mem (sp + 64) 64 = descriptor)
    (hdestination : memLoad mem (descriptor + 8) 64 = destination)
    (hdw : Writable code mem destination input.size)
    (hb : (span (sp + 152) input.size).HasBytes mem input)
    (hsep : (span (sp - 8) 176).Disjoint (span destination input.size))
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1,0⟩)
    (h39 : args[39] = ⟨32,args[39].get 32⟩)
    (h50 : args[50] = ⟨16,args[50].get 16⟩)
    (h51 : args[51] = ⟨16,args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l10294d else .l1024ed,args,mem⟩,[]⟩ ⟨next,[]⟩ ∧
      next.label = (if use256 then .l10295f else .l1024ff) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      RamWriteFrame mem next.store [span (sp - 8) 8,span destination input.size] ∧
      (span destination input.size).HasBytes next.store input := by
  have ns : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hroom)
  have low : sp.toNat + 168 ≤ 2^32 := by have hh := hw.readable.low; rw [ns] at hh; omega
  have nb : (sp + 152).toNat = sp.toNat + 152 := by bv_omega
  have ap := disjoint_bounds _ _ _ _ (by decide : 0 < 176) hpositive hsep
  rw [ns] at ap
  have n64 : (sp + 64).toNat = sp.toNat + 64 := by bv_omega
  have d8 : (descriptor + 8).toNat = descriptor.toNat + 8 := by have hh := hrdesc.low; bv_omega
  obtain ⟨callee,cont,run,label,target,guard,memory,c4,c7,c6,c2,c0,keep,typed⟩ :=
    tail_copy_out_runBlock use256 code hcode args mem
      (by rw [hsp]; exact hw.sub (Nat.le_refl _) (by omega))
      (by rw [hsp]; apply hw.readable.sub <;> rw [ns,n64] <;> omega)
      (by rw [hsp,hdescriptor]; apply hrdesc.sub <;> rw [d8] <;> omega) htarget
  have hf : RamWriteFrame mem callee.store [span (sp - 8) 8] := by
    rw [memory,hsp]
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨span (sp - 8) 8,by simp,?_⟩
    simp only [InRegion,span,ns]
    omega
  have bytes : (span (sp + 152) input.size).HasBytes callee.store input :=
    hasBytes_of_frame hf hb (by simp only [span,nb]; omega) (by
      intro r hin x hx hy
      obtain rfl := List.mem_singleton.mp hin
      simp only [span,MemoryRegion.Contains,nb,ns] at hx hy
      omega)
  have sp' : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [c4,hsp]; rfl
  have src' : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = sp + 152 := by rw [c6,hsource]; rfl
  have dst' : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = destination := by
    rw [c7,hsp,hdescriptor,hdestination]; rfl
  have count' : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = input.size := by rw [c2]; exact hcount
  have fp39 : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32,args[39].get 32⟩ := (keep 39 (by decide)).trans h39
  have fp50 : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16,args[50].get 16⟩ := (keep 50 (by decide)).trans h50
  have fp51 : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16,args[51].get 16⟩ := (keep 51 (by decide)).trans h51
  obtain ⟨output,exec,tag,ot,o4,ok,oframe,obytes⟩ := copy_exec code hcode callee.arguments callee.store
    (if use256 then 0x10295f else 0x1024ff) (sp + 152) destination input
    (typed hTypes) ((keep 22 (by decide)).trans hdf)
    (by rw [fp39]; rfl) (by rw [fp50]; rfl)
    (by rw [fp51]; rfl) src' dst' count'
    (by rw [sp']; exact (hw.readable.of_frame hf).sub (Nat.le_refl _) (by omega))
    (by rw [sp',memory,hsp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
    (by cases use256 <;> decide) (by rw [sp',ns]; omega)
    (by apply (hw.readable.of_frame hf).sub <;> rw [ns,nb] <;> omega) (hdw.of_frame hf) bytes
    (by rw [nb]; omega)
    (by
      apply RangeApart.of_toNat
      · have hh := hdw.readable.low
        omega
      · rw [sp',ns]
        omega
      · rw [sp',ns]
        omega)
  let next := cont.resume output
  have na : next.arguments = output.values := CFGCall.resume_arguments cont output
  have ex : LIR.program.Exec (dialect code) ⟨callee,[]⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label,callee.arguments,callee.store⟩,[]⟩ output
    rw [label]; exact exec
  have accept : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts,guard,tag]
    cases use256 <;> rfl
  have step : LIR.program.step (dialect code)
      ⟨⟨if use256 then .l10294d else .l1024ed,args,mem⟩,[]⟩ = .next ⟨callee,[cont]⟩ := by
    rw [Program.step,run]; rfl
  refine ⟨next,(Semantics.Reaches.single step).trans (CFGCall.exec_reaches_resume ex cont [] accept),
    by exact target,by simpa only [na] using ot,?_,?_,obytes⟩
  · intro r hin
    by_cases eq4 : r = 4
    · subst r
      rw [na]
      change output.values[4] = args[4]
      apply o4.trans
      rw [sp',show sp - 8 + 8 = sp by bv_omega]
      exact (congrArg (Value.mk 64) hsp.symm).trans (hTypes.value 4).symm
    · have nr4 : r.val ≠ 4 := by intro h; exact eq4 (Fin.ext h)
      have kept : r.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢
        omega
      rw [na]
      exact (ok r kept).trans (keep r kept)
  · have before : RamWriteFrame mem callee.store [span (sp - 8) 8,span destination input.size] := by
      apply (RamWriteFrame.refl _ _).trans hf
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      exact ⟨span (sp - 8) 8,by simp,Nat.le_refl _,Nat.le_refl _⟩
    change RamWriteFrame mem output.store _
    have after : RamWriteFrame callee.store output.store [span (sp - 8) 8,span destination input.size] := by
      simpa only [sp'] using oframe
    exact before.trans after (fun r hin ↦ ⟨r,hin,Nat.le_refl _,Nat.le_refl _⟩)

end AesGcm.Proofs.Machine.Core.Decrypt
