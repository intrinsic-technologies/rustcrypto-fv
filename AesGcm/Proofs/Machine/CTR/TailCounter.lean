import X86Proofs.Program.ReadWrite.RepString
import AesGcm.Proofs.Machine.Core.Memory
import AesGcm.Proofs.Machine.CTR.Outer.Invariant
import AesGcm.Proofs.Machine.CTR.TailSetup
import AesGcm.Proofs.Machine.CTR.TailCopy
import AesGcm.Proofs.Machine.CTR.Loop.CallResume
import AesGcm.Proofs.AES16.Encrypt
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.CTR.CounterMemory
import AesGcm.Proofs.Machine.CTR.CounterBlocks

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def tailCounterFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then .l1095ed else .l10814d, kept := #v[], arity := rfl,
    guard := some ⟨64, if use256 then 0x1095ed else 0x10814d⟩ }

def tailCounterMemory (mem : Ram) (sp counter ret : BitVec 64) : Ram :=
  let m1 := memStore mem (counter + 16) (memLoad mem (counter + 16) 32 + 1)
  let m2 := memStore m1 (sp + 256) (memLoad mem counter 64)
  let m3 := memStore m2 (sp + 264) (memLoad mem (counter + 8) 32)
  let m4 := memStore m3 (sp + 268)
    (bswapSpec (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32))
  memStore m4 (sp - 8) ret

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem tail_counter_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp counter : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hcounter : args[9].get 64 = counter)
    (hStack : Writable code mem (sp - 8) 280)
    (hCounter : Writable code mem counter 20) :
    ∃ callee,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1095b0 else .l108110), args, mem⟩ =
          .call callee (tailCounterFrame use256) ∧
      callee.label = (if use256 then .l106960 else .l105100) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[14].get 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[3].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[15].get 64⟩ ∧
      callee.store = tailCounterMemory mem sp counter
        (if use256 then 0x1095ed else 0x10814d) ∧
      (∀ r : Fin 53, r.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 280, span (counter + 16) 4] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hCounterRead := hCounter.readable
  have hCounterLow := hCounterRead.low
  have hRange {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1095b0 else 0x108110) 61 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108110 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1095b0 x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    runtime_context [hsp, hcounter]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l108110, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l1095b0, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hcounter, tailCounterFrame]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

set_option maxHeartbeats 800000 in
theorem tailCounterMemory_words (mem : Ram) (sp counter ret : BitVec 64)
    (q : Fin 4) :
    memLoad (tailCounterMemory mem sp counter ret)
      (sp + BitVec.ofNat 64 (256 + 4 * q.val)) 32 = counterWord mem counter 0 q := by
  rcases q with ⟨q, hq⟩
  have he : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl
  all_goals
    simp only [counterWord, Nat.reduceLT, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte,
      Fin.val_zero, BitVec.add_zero]
    unfold tailCounterMemory
    runtime_finish []
    all_goals first
      | rfl
      | (rw [BitVec.setWidth_eq_extractLsb' (by decide), extractLsb'_memLoad _ _ _ _ (by decide) (by decide) (by decide)]; rfl)
      | (rw [extractLsb'_memLoad _ _ _ _ (by decide) (by decide) (by decide)]; rfl)

set_option maxHeartbeats 400000 in
theorem tailCounterMemory_counter (mem : Ram) (sp counter ret : BitVec 64)
    (hStackLow : (sp - 8).toNat + 280 ≤ 2^32)
    (hCounterLow : counter.toNat + 20 ≤ 2^32)
    (hroom : 8 ≤ sp.toNat)
    (hApart : sp.toNat + 272 ≤ counter.toNat ∨ counter.toNat + 20 ≤ sp.toNat - 8) :
    memLoad (tailCounterMemory mem sp counter ret) (counter + 16) 32 =
      memLoad mem (counter + 16) 32 + 1 := by
  unfold tailCounterMemory
  runtime_finish []

theorem tailCounterMemory_block (mem : Ram) (sp counter ret : BitVec 64) :
    Fixslice.memoryBlock (tailCounterMemory mem sp counter ret) (sp + 256) =
      counterBlocks mem counter 0 := by
  funext j
  have hword := tailCounterMemory_words mem sp counter ret ⟨j.val / 4, by omega⟩
  have hb := congrArg (fun w : BitVec 32 ↦ (storedByte w (j.val % 4)).toBitVec) hword
  rw [storedByte_memLoad _ _ _ (by omega)] at hb
  change (memByte _ ((sp + 256) + BitVec.ofNat 64 j.val)).toBitVec = _
  have ha : sp + 256 + BitVec.ofNat 64 j.val =
      sp + BitVec.ofNat 64 (256 + 4 * (j.val / 4)) + BitVec.ofNat 64 (j.val % 4) := by
    change sp + BitVec.ofNat 64 256 + BitVec.ofNat 64 j.val = _
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply congrArg (fun n : Nat ↦ sp + BitVec.ofNat 64 n)
    omega
  rw [ha]
  exact hb


open Standards.NIST.GCM

set_option maxHeartbeats 1200000 in
theorem tail_encrypt_block (u : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant u).keyBytes) (loc : LIR.lifted.Location)
    (sp lower counter schedule : BitVec 64)
    (hl : loc.label = (if u then .l1095b0 else .l108110)) (ht : GPRsTyped loc.arguments)
    (s4 : loc.arguments[4]'(by change 4 < 53; decide) = ⟨64,sp⟩)
    (s9 : loc.arguments[9]'(by change 9 < 53; decide) = ⟨64,counter⟩)
    (s3 : loc.arguments[3]'(by change 3 < 53; decide) = ⟨64,schedule⟩)
    (s14 : loc.arguments[14]'(by change 14 < 53; decide) = ⟨64,sp+152⟩)
    (s15 : loc.arguments[15]'(by change 15 < 53; decide) = ⟨64,sp+256⟩)
    (s22 : loc.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩)
    (s39 : loc.arguments[39]'(by change 39 < 53; decide) = ⟨32,(loc.arguments[39]'(by change 39 < 53; decide)).get 32⟩)
    (s50 : loc.arguments[50]'(by change 50 < 53; decide) = ⟨16,(loc.arguments[50]'(by change 50 < 53; decide)).get 16⟩)
    (s51 : loc.arguments[51]'(by change 51 < 53; decide) = ⟨16,(loc.arguments[51]'(by change 51 < 53; decide)).get 16⟩)
    (low : lower.toNat + (if u then 376 else 360) = sp.toNat)
    (aligned : sp.toNat % 16 = 0)
    (stack : Writable code loc.store lower (if u then 648 else 632))
    (cw : Writable code loc.store counter 20)
    (sched : AES16.ScheduleIn (AES16.variant u) key schedule loc.store)
    (sr : Readable loc.store schedule (16*((AES16.variant u).Nr+1)))
    (cs : sp.toNat+272 ≤ counter.toNat ∨ counter.toNat+20 ≤ lower.toNat)
    (ss : sp.toNat+272 ≤ schedule.toNat ∨ schedule.toNat+16*((AES16.variant u).Nr+1) ≤ lower.toNat)
    (sc : counter.toNat+20 ≤ schedule.toNat ∨ schedule.toNat+16*((AES16.variant u).Nr+1) ≤ counter.toNat)
    (slots : 0x201238 ≤ lower.toNat ∨ sp.toNat+272 ≤ 0x201210)
    (counterSlots : ∀ p ∈ ([0x201210,0x201230] : List (BitVec 64)),
      counter.toNat+20 ≤ p.toNat ∨ p.toNat+8 ≤ counter.toNat)
    (r1 : Readable loc.store 0x201210 8) (r2 : Readable loc.store 0x201230 8)
    (v1 : memLoad loc.store 0x201210 64 = 0x103880) (v2 : memLoad loc.store 0x201230 64 = 0x101230) :
    ∃ out : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨out,[]⟩ ∧
      out.label = (if u then .l1095ed else .l10814d) ∧ GPRsTyped out.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → out.arguments[r] = loc.arguments[r]) ∧
      Fixslice.memoryBlock out.store (sp+152) =
        Fixslice16.fromStandard (Standards.NIST.AES.cipher (AES16.variant u) key (initialCounterBlock loc.store counter)) ∧
      memLoad out.store (counter+16) 32 = memLoad loc.store (counter+16) 32 + 1 ∧
      RamWriteFrame loc.store out.store [span lower (if u then 376 else 360),
        span (sp+152) 16, span (sp+256) 16, span (counter+16) 4] := by
  rcases loc with ⟨label,args,mem⟩
  dsimp only at hl
  subst label
  let n : Nat := if u then 376 else 360
  let w : Nat := if u then 648 else 632
  let info := if u then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo
  let ret : BitVec 64 := if u then 0x1095ed else 0x10814d
  change lower.toNat + n = sp.toNat at low
  change Writable code mem lower w at stack
  have sizes : w = n+272 ∧ n = info.window+8 ∧ 360 ≤ n := by cases u <;> decide
  have bound := stack.readable.low
  have clow := cw.readable.low
  have slow := sr.low
  have sub8 : (sp-8).toNat = sp.toNat-8 := by bv_omega
  have ctr16 : (counter+16).toNat = counter.toNat+16 := by bv_omega
  have addSp (k : Nat) (hk : k ≤ 272) : (sp+BitVec.ofNat 64 k).toNat = sp.toNat+k :=
    toNat_add_ofNat sp k (by omega)
  have a152 : (sp+152).toNat = sp.toNat+152 := addSp 152 (by decide)
  have a256 : (sp+256).toNat = sp.toNat+256 := addSp 256 (by decide)
  have a264 : (sp+264).toNat = sp.toNat+264 := addSp 264 (by decide)
  have a268 : (sp+268).toNat = sp.toNat+268 := addSp 268 (by decide)
  have substack : Writable code mem (sp-8) 280 := stack.sub (by omega) (by omega)
  obtain ⟨callee,hcall,cl,c4,c7,c6,c2,cm,keep,ct,cf⟩ :=
    tail_counter_call u code hcode args mem sp counter ht (congrArg (Value.get 64) s4)
      (congrArg (Value.get 64) s9) substack cw
  let af := activationOfValues callee.store callee.arguments ret lower
  have al : af.low = lower := rfl
  have asp : af.rsp = sp-8 := congrArg (Value.get 64) c4
  have adst : af.rdi = sp+152 := by
    change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _
    rw [c7]; exact congrArg (Value.get 64) s14
  have asrc : af.rsi = schedule := by
    change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _
    rw [c6]; exact congrArg (Value.get 64) s3
  have ain : af.rdx = sp+256 := by
    change (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = _
    rw [c2]; exact congrArg (Value.get 64) s15
  have align : af.rsp.toNat % 16 = 8 := by rw [asp,sub8]; omega
  have room : lower.toNat+info.window ≤ af.rsp.toNat := by rw [asp,sub8]; omega
  have childaddr : af.rsp - BitVec.ofNat 64 info.window = lower := by
    apply BitVec.eq_of_toNat_eq
    have le : BitVec.ofNat 64 info.window ≤ af.rsp := by
      change info.window % 2^64 ≤ af.rsp.toNat
      omega
    rw [BitVec.toNat_sub_of_le le, BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),asp,sub8]
    omega
  have childw : Writable code callee.store (af.rsp - BitVec.ofNat 64 info.window) info.window := by
    rw [childaddr]
    exact (stack.of_frame cf).sub (Nat.le_refl _) (by omega)
  have retread : Readable callee.store af.rsp 8 := by
    rw [asp]; exact (substack.readable.of_frame cf).sub (Nat.le_refl _) (by omega)
  have retload : memLoad callee.store af.rsp 64 = ret := by
    rw [asp,cm]
    exact memLoad_memStore_eq _ _ rfl (by decide) (by decide)
  have schedOut : Outside [span (sp-8) 280, span (counter+16) 4] schedule (16*((AES16.variant u).Nr+1)) := by
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span,sub8,ctr16] <;> omega
  have pre : AES16.ScheduleIn (AES16.variant u) key af.rsi callee.store ∧
      Readable callee.store af.rsi (16*((AES16.variant u).Nr+1)) ∧
      Readable callee.store af.rdx 16 ∧ Fixslice.memoryBlock callee.store af.rdx =
        Fixslice16.fromStandard (initialCounterBlock mem counter) ∧
      Writable code callee.store af.rdi 16 ∧
      (callStack af).Disjoint (span af.rdi 16) ∧ (callStack af).Disjoint (span af.rdx 16) ∧
      (callStack af).Disjoint (span af.rsi (16*((AES16.variant u).Nr+1))) := by
    rw [asrc,ain,adst]
    refine ⟨AES16.scheduleIn_of_frame sched cf schedOut, sr.of_frame cf, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (stack.readable.of_frame cf).sub (by omega)
        (by omega)
    · rw [cm,tailCounterMemory_block]
      funext i
      simp only [counterBlocks,Fixslice16.fromStandard,initialCounterBlock,Vector.getElem_ofFn]
    · exact (stack.of_frame cf).sub (by omega)
        (by omega)
    all_goals intro x hx hy; simp only [MemoryRegion.Contains,callStack,span,al,asp,sub8] at hx hy
    · omega
    · omega
    · omega
  have slotOut (p : BitVec 64) (hp : p ∈ ([0x201210,0x201230] : List (BitVec 64))) :
      Outside [span (sp-8) 280,span (counter+16) 4] p 8 := by
    have apart := counterSlots p hp
    have bounds : 0x201210 ≤ p.toNat ∧ p.toNat + 8 ≤ 0x201238 := by
      simp only [List.mem_cons,List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> decide
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span,sub8,ctr16] <;> omega
  have values : Atom.All code callee.arguments callee.store (info.callSlotAtoms info.callSlots af) := by
    have l1 := (cf.memLoad_eq (k := 64) (slotOut 0x201210 (by decide))).trans v1
    have l2 := (cf.memLoad_eq (k := 64) (slotOut 0x201230 (by decide))).trans v2
    have apart : 0x201238 + info.window ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201210 := by
      rw [asp,sub8]; omega
    cases u <;> exact ⟨r1.of_frame cf,l1,r2.of_frame cf,l2,apart,trivial⟩
  have preserved39 : (callee.arguments[39]'(by change 39 < 53; decide)) = args[39]'(by change 39 < 53; decide) := keep 39 (by decide)
  have preserved50 : (callee.arguments[50]'(by change 50 < 53; decide)) = args[50]'(by change 50 < 53; decide) := keep 50 (by decide)
  have preserved51 : (callee.arguments[51]'(by change 51 < 53; decide)) = args[51]'(by change 51 < 53; decide) := keep 51 (by decide)
  obtain ⟨out,exec,tag,done,typ,frame,result⟩ :=
    callContract_exec_values LIR.lifted code _ info (fun f ↦ [span f.rdi 16]) _ _
      (AES16.encrypt_callContract u code hcode key (initialCounterBlock mem counter))
      callee.store callee.arguments ret lower ct
      (by rw [preserved39]; exact s39) (by rw [preserved50]; exact s50)
      (by rw [preserved51]; exact s51) ((keep 22 (by decide)).trans s22)
      retread retload (by cases u <;> decide)
      (fun _ ↦ childw) room align values pre
  change Atom.All code out.values out.store (info.doneAtoms af) at done
  change RamWriteFrame callee.store out.store [af.region,span af.rdi 16] at frame
  change Fixslice.memoryBlock out.store af.rdi = _ at result
  refine ⟨⟨_,out.values,out.store⟩, Loop.call_contract_resume hcall cl exec tag, rfl,typ,?_,adst ▸ result,?_,?_⟩
  · have ho : out.values[4] = ⟨64, af.rsp+8⟩ ∧ out.values[22] = ⟨1,0⟩ ∧
        out.values[3] = ⟨64, af.rbx⟩ ∧ out.values[5] = ⟨64, af.rbp⟩ ∧
        out.values[12] = ⟨64,af.r12⟩ ∧ out.values[13] = ⟨64,af.r13⟩ ∧
        out.values[14] = ⟨64,af.r14⟩ ∧ out.values[15] = ⟨64,af.r15⟩ ∧
        out.values[39] = ⟨32,af.mxcsr⟩ ∧ out.values[50] = ⟨16,af.ftw⟩ ∧
        out.values[51] = ⟨16,af.fcw⟩ ∧ True := by cases u <;> exact done
    obtain ⟨o4,o22,o3,o5,o12,o13,o14,o15,o39,o50,o51,_⟩ := ho
    have restored (r : Fin 16) (hr : r.val ∈ [3,5,12,13,14,15]) :
        (⟨64,(callee.arguments[r.val]'(by change r.val < 53; have := r.isLt; omega)).get 64⟩ : Value) =
        args[r.val]'(by change r.val < 53; have := r.isLt; omega) := by
      have hk := keep ⟨r.val, by have := r.isLt; omega⟩ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h <;> simp only [h] <;> decide)
      exact (congrArg (fun v : Value ↦ Value.mk 64 (v.get 64)) hk).trans (ht.value r).symm
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact o3.trans (restored 3 (by decide))
    · have eq : af.rsp+8 = sp := by rw [asp]; bv_omega
      exact (o4.trans (congrArg (Value.mk 64) eq)).trans s4.symm
    · exact o5.trans (restored 5 (by decide))
    · exact o12.trans (restored 12 (by decide))
    · exact o13.trans (restored 13 (by decide))
    · exact o14.trans (restored 14 (by decide))
    · exact o15.trans (restored 15 (by decide))
    · exact o22.trans s22.symm
    · exact (o39.trans (congrArg (fun v : Value ↦ Value.mk 32 (v.get 32)) preserved39)).trans s39.symm
    · exact (o50.trans (congrArg (fun v : Value ↦ Value.mk 16 (v.get 16)) preserved50)).trans s50.symm
    · exact (o51.trans (congrArg (fun v : Value ↦ Value.mk 16 (v.get 16)) preserved51)).trans s51.symm
  · have outCounter : Outside [af.region,span af.rdi 16] (counter+16) 4 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Activation.region,span,asp,al,adst,sub8,ctr16,a152] <;> omega
    rw [frame.memLoad_eq (k := 32) outCounter,cm]
    exact tailCounterMemory_counter _ _ _ _ substack.readable.low clow (by omega) (by omega)
  · let regs := [span lower n,span (sp+152) 16,span (sp+256) 16,span (counter+16) 4]
    have before : RamWriteFrame mem callee.store regs := by
      rw [cm]
      unfold tailCounterMemory
      repeat' apply RamWriteFrame.memStore
      · exact RamWriteFrame.refl _ _
      · refine ⟨span (counter+16) 4,by simp [regs],?_,?_,?_⟩ <;> simp only [span,ctr16] <;> omega
      · refine ⟨span (sp+256) 16,by simp [regs],?_,?_,?_⟩ <;> simp only [span,a256] <;> omega
      · refine ⟨span (sp+256) 16,by simp [regs],?_,?_,?_⟩ <;> simp only [span,a256,a264] <;> omega
      · refine ⟨span (sp+256) 16,by simp [regs],?_,?_,?_⟩ <;> simp only [span,a256,a268] <;> omega
      · refine ⟨span lower n,by simp [regs],?_,?_,?_⟩ <;> simp only [span,sub8] <;> omega
    apply before.trans frame
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨span lower n,by simp [regs],by simp only [Activation.region,span,al]; omega,
        by simp only [Activation.region,span,al,asp,sub8]; omega⟩
    · rw [adst]
      exact ⟨span (sp+152) 16,by simp [regs],Nat.le_refl _,Nat.le_refl _⟩

private theorem tail_keystream_geometry (u : Bool) (code : CodeMap) (fr : Activation)
    (key : Vector UInt8 (AES16.variant u).keyBytes) (input : ByteArray) (count : Nat)
    (hn : 0 < input.size) (schedule counter src dst : BitVec 64) (exit : LIR.lifted.Location)
    (h : OuterExit u code fr key input count schedule counter src dst exit) :
    let sp := outerStackPointer fr u
    let lower := fr.rsp - (if u then 2688 else 2160)
    lower.toNat + (if u then 376 else 360) = sp.toNat ∧ sp.toNat % 16 = 0 ∧
    Writable code exit.store lower (if u then 648 else 632) ∧
    (sp.toNat+272 ≤ counter.toNat ∨ counter.toNat+20 ≤ lower.toNat) ∧
    (sp.toNat+272 ≤ schedule.toNat ∨ schedule.toNat+16*((AES16.variant u).Nr+1) ≤ lower.toNat) ∧
    (counter.toNat+20 ≤ schedule.toNat ∨ schedule.toNat+16*((AES16.variant u).Nr+1) ≤ counter.toNat) ∧
    (0x201238 ≤ lower.toNat ∨ sp.toNat+272 ≤ 0x201210) ∧
    (∀ p ∈ ([0x201210,0x201230] : List (BitVec 64)), counter.toNat+20 ≤ p.toNat ∨ p.toNat+8 ≤ counter.toNat) ∧
    Outside [fr.region, span (counter+16) 4, span dst input.size] counter 16 ∧
    exit.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩ ∧
    exit.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ ∧
    exit.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ ∧
    exit.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ := by
  intro sp lower
  let w : Nat := if u then 2688 else 2160
  let d : Nat := if u then 2312 else 1800
  let s := 16 * ((AES16.variant u).Nr + 1)
  have sw : 0 < s := by dsimp [s]; omega
  have frame : Atom.All code exit.arguments exit.store
      (if u then LIR.Fn1084e0.frameAt .l109509 fr else LIR.Fn107050.frameAt .l10805f fr) := by
    have e := h.frame
    cases u <;> simpa only [cryptFrameAt, h.label, Bool.false_eq_true, ↓reduceIte] using e
  have facts : Writable code exit.store lower w ∧ fr.low.toNat + w ≤ fr.rsp.toNat ∧
      fr.rsp.toNat % 16 = 8 ∧
      exit.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩ ∧
      exit.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ ∧
      exit.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ ∧
      exit.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ := by
    cases u <;> obtain ⟨_,df,mx,ft,fc,_,_,_,_,_,_,_,_,_,st,rm,al,_⟩ := frame <;>
      exact ⟨st,rm,al,df,mx,ft,fc⟩
  obtain ⟨st,rm,al,regs⟩ := facts
  have spN : sp.toNat = fr.rsp.toNat - d := by
    cases u <;> exact stack_sub_toNat fr rm (by decide)
  have lowerN : lower.toNat = fr.rsp.toNat - w := by
    cases u <;> exact stack_sub_toNat fr rm (Nat.le_refl _)
  have dims : w = d + (if u then 376 else 360) ∧ d ≥ 272 ∧
      (if u then 648 else 632) ≤ w ∧ 0 < w := by cases u <;> decide
  obtain ⟨wD,d272,szw,wpos⟩ := dims
  have stSep : ∀ r ∈ [span fr.rdi 8,span fr.rsi 32,span schedule s,span counter 20,
      span src input.size,span dst input.size], (callStack fr).Disjoint r :=
    atomsAll_mem (atom := .fact _) h.outer (by simp only [outerAtoms,s,List.mem_cons,true_or,or_true])
  have cSep : ∀ r ∈ [span fr.rdi 8,span fr.rsi 32,span schedule s,
      span src input.size,span dst input.size], (span counter 20).Disjoint r :=
    atomsAll_mem (atom := .fact _) h.outer (by simp only [outerAtoms,s,List.mem_cons,true_or,or_true])
  have slotsSep : ∀ p ∈ ([0x201208,0x201210,0x201230] : List (BitVec 64)),
      (span dst input.size).Disjoint (span p 8) ∧ (span counter 20).Disjoint (span p 8) :=
    atomsAll_mem (atom := .fact _) h.outer (by simp only [outerAtoms,List.mem_cons,true_or,or_true])
  have slotsStack : (if u then 0x201cb8 else 0x201aa8) ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 :=
    atomsAll_mem (atom := .fact _) h.outer (by simp only [outerAtoms,List.mem_cons,true_or,or_true])
  have stackBounds (p : BitVec 64) (n : Nat) (npos : 0 < n)
      (sep : (callStack fr).Disjoint (span p n)) :
      fr.rsp.toNat+8 ≤ p.toNat ∨ p.toNat+n ≤ fr.low.toNat := by
    have b := disjoint_bounds fr.low.toNat (fr.rsp.toNat+8-fr.low.toNat) p.toNat n
      (by omega) npos sep
    omega
  have cs := stackBounds counter 20 (by decide) (stSep _ (by simp))
  have ss := stackBounds schedule s sw (stSep _ (by simp))
  have cd := disjoint_bounds counter.toNat 20 dst.toNat input.size (by decide) hn (cSep (span dst input.size) (by simp))
  have cLow := h.toOuterState.counter_write.readable.low
  have c16 : (counter+16).toNat = counter.toNat + 16 := by
    simp only [BitVec.toNat_add, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, ?_, st.sub (by omega) (by omega), by omega, ?_, ?_, ?_, ?_, ?_, regs⟩
  · cases u <;> simp only [d, w, Bool.false_eq_true, ↓reduceIte] at spN rm <;> omega
  · change sp.toNat+272 ≤ schedule.toNat ∨ schedule.toNat+s ≤ lower.toNat
    omega
  · exact disjoint_bounds counter.toNat 20 schedule.toNat s (by decide) sw (cSep (span schedule s) (by simp))
  · cases u <;> simp only [d, w, Bool.false_eq_true, ↓reduceIte] at spN lowerN slotsStack <;> omega
  · intro p hp
    exact disjoint_bounds counter.toNat 20 p.toNat 8 (by decide) (by decide)
      ((slotsSep p (List.mem_cons_of_mem _ hp)).2)
  · refine ⟨by omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Activation.region, span, c16] <;> omega

private theorem tail_keystream_copy (mem copyBefore : Ram) (sp lower counter : BitVec 64)
    (room k : Nat) (f : Nat → UInt8) (b : Standards.NIST.AES.Block)
    (low : lower.toNat + room = sp.toNat) (top : sp.toNat + 272 ≤ 2^32)
    (hk : k < 3) (apart : sp.toNat+272 ≤ counter.toNat ∨ counter.toNat+20 ≤ lower.toNat)
    (clow : counter.toNat+20 ≤ 2^32)
    (prefixBytes : ∀ i < 16*k, memByte mem (sp+8+BitVec.ofNat 64 i) = f i)
    (frame : RamWriteFrame mem copyBefore [span lower room, span (sp+152) 16,
      span (sp+256) 16, span (counter+16) 4])
    (read : Readable copyBefore (sp+152) 16)
    (block : Fixslice.memoryBlock copyBefore (sp+152) = Fixslice16.fromStandard b)
    (expected : ∀ j : Fin 16, b[j.val] = f (16*k+j.val)) :
    ∀ i < 16*(k+1), memByte
      (copyTagWords copyBefore (sp + BitVec.ofNat 64 (16*k) + 8) (sp+152))
      (sp+8+BitVec.ofNat 64 i) = f i := by
  let dest := sp + BitVec.ofNat 64 (16*k) + 8
  have s8 : (sp+8).toNat = sp.toNat+8 := toNat_add_ofNat sp 8 (by omega)
  have s152 : (sp+152).toNat = sp.toNat+152 := toNat_add_ofNat sp 152 (by omega)
  have s256 : (sp+256).toNat = sp.toNat+256 := toNat_add_ofNat sp 256 (by omega)
  have c16 : (counter+16).toNat = counter.toNat+16 := toNat_add_ofNat counter 16 (by omega)
  have sk := toNat_add_ofNat sp (16*k) (by omega)
  have destN : dest.toNat = sp.toNat+16*k+8 := by
    change (sp+BitVec.ofNat 64 (16*k)+8).toNat = _
    rw [show (sp+BitVec.ofNat 64 (16*k)+8).toNat = (sp+BitVec.ofNat 64 (16*k)).toNat+8
      from toNat_add_ofNat _ 8 (by omega), sk]
  have hb := Core.hasBytes_of_memoryBlock read block
  have copied := copyTagWords_hasBytes copyBefore dest (sp+152) ⟨b.toArray⟩ hb
  have cf := copyTagWords_frame copyBefore dest (sp+152) (by omega)
  intro i hi
  have pos := toNat_add_ofNat (sp+8) i (by omega)
  by_cases before : i < 16*k
  · have ho : Outside [span lower room,span (sp+152) 16,span (sp+256) 16,span (counter+16) 4]
        (sp+8+BitVec.ofNat 64 i) 1 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [span] <;> omega
    have hco : Outside [span dest 16] (sp+8+BitVec.ofNat 64 i) 1 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      left
      change _ ≤ dest.toNat
      omega
    change memByte (copyTagWords copyBefore dest _) _ = _
    rw [← prefixBytes i before]
    exact congrArg (fun v : Option UInt8 ↦ v.getD 0) ((cf.outside _ hco).trans (frame.outside _ ho))
  · let j : Fin 16 := ⟨i - 16*k, by omega⟩
    have jN : 16*k+j.val = i := by dsimp [j]; omega
    have hj := copied.2 ⟨j.val, by simpa only [ByteArray.size, Vector.size_toArray] using j.isLt⟩
    change (copyTagWords copyBefore dest (sp+152))[BitVec.ofNat 64 (dest.toNat+j.val)]? = some b[j.val] at hj
    have addr : sp+8+BitVec.ofNat 64 i = BitVec.ofNat 64 (dest.toNat+j.val) := by
      apply BitVec.eq_of_toNat_eq
      simp only [pos, s8, BitVec.toNat_ofNat, destN, Nat.mod_eq_of_lt (by omega : sp.toNat+16*k+8+j.val < 2^64)]
      omega
    change memByte (copyTagWords copyBefore dest _) _ = _
    rw [addr]
    simp only [memByte, PhysicalMemory.read, hj, Option.getD_some, expected, jN]

set_option maxHeartbeats 2200000 in
theorem tail_keystream (use256 : Bool) (code : CodeMap) (fr : Activation)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (input : ByteArray)
    (count : Nat) (hsize : input.size = 16 * count) (hn : count % 4 ≠ 0)
    (schedule counter src dst : BitVec 64) (exit : LIR.lifted.Location)
    (h : OuterExit use256 code fr key input count schedule counter src dst exit) :
    let sp := outerStackPointer fr use256
    let offset := BitVec.ofNat 64 (input.size - input.size % 64)
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨exit, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l109618 else .l108178) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next.arguments[r] = exit.arguments[r]) ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 64 = src + offset ∧
      memLoad next.store (sp + 216) 64 = dst + offset ∧
      memLoad next.store (sp + 232) 64 = BitVec.ofNat 64 (count % 4) ∧
      memLoad next.store (counter+16) 32 = memLoad fr.original (counter+16) 32 + BitVec.ofNat 32 count ∧
      RamWriteFrame exit.store next.store
        [span (fr.rsp - (if use256 then 2688 else 2160)) (if use256 then 648 else 632),
         span (counter + 16) 4] ∧
      ∀ i < input.size % 64, memByte next.store (sp + 8 + BitVec.ofNat 64 i) =
        (Standards.NIST.AES.cipher (AES16.variant use256) key
          (bytesOfBits (Nat.repeat (inc 32) ((input.size - input.size % 64 + i) / 16)
            (bitsOfBytes (initialCounterBlock fr.original counter)))))[i % 16]'(by omega) := by
  let sp := outerStackPointer fr use256
  let lower := fr.rsp - (if use256 then 2688 else 2160)
  let room : Nat := if use256 then 376 else 360
  let size : Nat := if use256 then 648 else 632
  let regs : List Nat := [3,4,5,12,14,15,22,39,50,51]
  let rem := count % 4
  let base := 4 * (count / 4)
  let offset := input.size - input.size % 64
  let work := [span lower size, span (counter + 16) 4]
  let keyByte (i : Nat) := (Standards.NIST.AES.cipher (AES16.variant use256) key
    (bytesOfBits (Nat.repeat (inc 32) ((offset + i) / 16)
      (bitsOfBytes (initialCounterBlock fr.original counter)))))[i % 16]'(by omega)
  have nrem : 0 < rem ∧ rem < 4 := by dsimp [rem]; omega
  have ncount : base + rem = count := by dsimp [base,rem]; omega
  have noff : offset = 16 * base := by dsimp [offset,base]; omega
  have ntail : input.size % 64 = 16 * rem := by dsimp [rem]; omega
  obtain ⟨low,aligned,stack,cs,ss,sc,slotSep,ctrSlots,originalOut,e22,e39,e50,e51⟩ :=
    tail_keystream_geometry use256 code fr key input count (by omega) schedule counter src dst exit h
  change lower.toNat + room = sp.toNat at low
  change sp.toNat % 16 = 0 at aligned
  change Writable code exit.store lower size at stack
  change sp.toNat+272 ≤ counter.toNat ∨ counter.toNat+20 ≤ lower.toNat at cs
  change sp.toNat+272 ≤ schedule.toNat ∨ schedule.toNat+16*((AES16.variant use256).Nr+1) ≤ lower.toNat at ss
  change 0x201238 ≤ lower.toNat ∨ sp.toNat+272 ≤ 0x201210 at slotSep
  have geom : size = room + 272 ∧ 360 ≤ room := by cases use256 <;> decide
  have slim := stack.readable.low
  have clim := h.toOuterState.counter_write.readable.low
  have sn (n : Nat) (hh : n ≤ 272) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat+n :=
    toNat_add_ofNat sp n (by omega)
  have cn : (counter+16).toNat = counter.toNat+16 := toNat_add_ofNat counter 16 (by omega)
  have s8 : (sp+8).toNat = sp.toNat+8 := sn 8 (by decide)
  have s152 : (sp+152).toNat = sp.toNat+152 := sn 152 (by decide)
  have s216 : (sp+216).toNat = sp.toNat+216 := sn 216 (by decide)
  have s232 : (sp+232).toNat = sp.toNat+232 := sn 232 (by decide)
  have s248 : (sp+248).toNat = sp.toNat+248 := sn 248 (by decide)
  have s256 : (sp+256).toNat = sp.toNat+256 := sn 256 (by decide)
  have narrow (p : BitVec 64) (n : Nat) (bound : p.toNat+n ≤ 2^64)
      (a : sp.toNat+272 ≤ p.toNat ∨ p.toNat+n ≤ lower.toNat)
      (b : counter.toNat+20 ≤ p.toNat ∨ p.toNat+n ≤ counter.toNat+16) :
      Outside work p n := by
    refine ⟨bound, ?_⟩
    intro r hr
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span,cn] <;> omega
  have cout := narrow counter 16 (by omega) (by omega) (by omega)
  have sout := narrow schedule (16*((AES16.variant use256).Nr+1))
    (by have := h.schedule_read.low; omega) ss (by omega)
  have slotOut (p : BitVec 64) (hp : p ∈ [0x201210,0x201230]) : Outside work p 8 := by
    have b := ctrSlots p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      apply narrow <;> simp only [BitVec.reduceToNat] at * <;> omega
  have remSlot : memLoad exit.store (sp+232) 64 = BitVec.ofNat 64 rem :=
    atomsAll_mem (atom := .mem (sp+232) 64 _) h.outer
      (by simp only [rem,sp,outerAtoms,List.mem_cons,true_or,or_true])
  have ctrSlot : memLoad exit.store (sp+248) 64 = counter :=
    atomsAll_mem (atom := .mem (sp+248) 64 _) h.outer
      (by simp only [sp,outerAtoms,List.mem_cons,true_or,or_true])
  obtain ⟨first,reach0,label0,typed0,keep0,f5,f3,f12,f13,f14,f15,dst0,fw0⟩ :=
    tail_keystream_setup use256 code fr hcode key input count hsize hn schedule counter src dst exit h
  change RamWriteFrame exit.store first.store [span (sp+8) 64, span (sp+216) 8] at fw0
  let P (k : Nat) := ∃ loc : LIR.lifted.Location,
    (LIR.program.sem (dialect code)).Reaches ⟨exit,[]⟩ ⟨loc,[]⟩ ∧
    loc.label = (if k = rem then (if use256 then .l109618 else .l108178) else
      (if use256 then .l1095b0 else .l108110)) ∧ GPRsTyped loc.arguments ∧
    (∀ r : Fin 53, r.val ∈ regs → loc.arguments[r] = first.arguments[r]) ∧
    loc.arguments[9]'(by change 9 < 53; decide) = ⟨64,counter⟩ ∧
    loc.arguments[13]'(by change 13 < 53; decide) = ⟨64,BitVec.ofNat 64 (16*k)⟩ ∧
    memLoad loc.store (sp+216) 64 = dst + BitVec.ofNat 64 offset ∧
    memLoad loc.store (sp+232) 64 = BitVec.ofNat 64 rem ∧
    memLoad loc.store (sp+248) 64 = counter ∧
    memLoad loc.store (counter+16) 32 = memLoad fr.original (counter+16) 32 + BitVec.ofNat 32 (base+k) ∧
    RamWriteFrame exit.store loc.store work ∧
    ∀ i < 16*k, memByte loc.store (sp+8+BitVec.ofNat 64 i) = keyByte i
  have start : P 0 := by
    have out {p : BitVec 64} {n : Nat} (hb : p.toNat+n ≤ 2^64)
        (sep : p.toNat+n ≤ sp.toNat+8 ∨ sp.toNat+224 ≤ p.toNat) :
        Outside [span (sp+8) 64,span (sp+216) 8] p n := by
      refine ⟨hb, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [span] <;> omega
    refine ⟨first,reach0,by simpa only [ite_eq_right (show 0 ≠ rem by omega)] using label0,
      typed0,fun _ _ ↦ rfl,(keep0 9 (by decide)).trans h.toOuterState.counter,f13,dst0,
      (fw0.memLoad_eq (out (by change (sp+232).toNat+8 ≤ _; omega) (by change _+8 ≤ _ ∨ _ ≤ _; omega))).trans remSlot,
      (fw0.memLoad_eq (out (by change (sp+248).toNat+8 ≤ _; omega) (by change _+8 ≤ _ ∨ _ ≤ _; omega))).trans ctrSlot,
      (fw0.memLoad_eq (out (by change (counter+16).toNat+4 ≤ _; omega) (by change _+4 ≤ _ ∨ _ ≤ _; omega))).trans h.counter_value,
      (RamWriteFrame.refl _ _).trans fw0 ?_, by intro i hi; omega⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨span lower size, by simp [work], ?_, ?_⟩ <;>
      simp only [span] <;> omega
  have preserved {loc : LIR.lifted.Location}
      (keep : ∀ r : Fin 53, r.val ∈ regs → loc.arguments[r] = first.arguments[r])
      (r : Fin 53) (hr : r.val ∈ [4,22,39,50,51]) : loc.arguments[r] = exit.arguments[r] := by
    apply (keep r ?_).trans (keep0 r ?_)
    all_goals simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    all_goals omega
  have advance (k : Nat) (hk : k < rem) (prev : P k) : P (k+1) := by
    obtain ⟨loc,reach,label,typed,keep,r9,r13,ds,rs,cslt,val,frame,bytes⟩ := prev
    rw [ite_eq_right (by omega : k ≠ rem)] at label
    have r4 := (preserved keep 4 (by decide)).trans h.toOuterState.stackPointer
    have r39 : loc.arguments[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ :=
      (preserved keep 39 (by decide)).trans e39
    have r50 : loc.arguments[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ :=
      (preserved keep 50 (by decide)).trans e50
    have r51 : loc.arguments[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ :=
      (preserved keep 51 (by decide)).trans e51
    obtain ⟨out,reachA,labA,typA,keepA,block,incA,aFrame⟩ := tail_encrypt_block use256 code hcode
      key loc sp lower counter schedule label typed r4 r9 ((keep 3 (by decide)).trans f3)
      ((keep 14 (by decide)).trans f14) ((keep 15 (by decide)).trans f15) ((preserved keep 22 (by decide)).trans e22)
      (by rw [r39]; rfl) (by rw [r50]; rfl)
      (by rw [r51]; rfl) low aligned (stack.of_frame frame)
      (h.toOuterState.counter_write.of_frame frame) (AES16.scheduleIn_of_frame h.schedule_in frame sout)
      (h.schedule_read.of_frame frame) cs ss sc slotSep ctrSlots
      (h.toOuterState.slot1_readable.of_frame frame) (h.toOuterState.slot2_readable.of_frame frame)
      ((frame.memLoad_eq (slotOut _ (by decide))).trans h.toOuterState.slot1_value)
      ((frame.memLoad_eq (slotOut _ (by decide))).trans h.toOuterState.slot2_value)
    have unchanged (n : Nat) (hn : n + 4 ≤ 16) :
        memLoad loc.store (counter + BitVec.ofNat 64 n) 32 =
          memLoad fr.original (counter + BitVec.ofNat 64 n) 32 :=
      (frame.memLoad_eq (outside_subregion cout (by omega) (by change n+4 ≤ 16; omega))).trans
        (h.written.memLoad_eq (outside_subregion originalOut (by omega) (by change n+4 ≤ 16; omega)))
    have advanced := initialCounterBlock_advance fr.original loc.store counter (base + k)
      (fun j ↦ unchanged (4*j.val) (by have := j.isLt; omega)) (unchanged 12 (by decide)) val
    have inputEq : initialCounterBlock loc.store counter =
        bytesOfBits (Nat.repeat (inc 32) (base+k) (bitsOfBytes (initialCounterBlock fr.original counter))) := by
      rw [← advanced, AesGcm.Proofs.bytesOfBits_bitsOfBytes]
    have cipherByte (j : Fin 16) : (Standards.NIST.AES.cipher (AES16.variant use256) key
        (initialCounterBlock loc.store counter))[j.val] = keyByte (16*k+j.val) := by
      have index : (offset + (16*k+j.val)) / 16 = base+k := by omega
      have byteIndex : (16*k+j.val) % 16 = j.val := by omega
      simp only [keyByte, inputEq, index, byteIndex]
    let idx := BitVec.ofNat 64 (16*k)
    let len := BitVec.ofNat 64 (16*rem)
    let addr := sp + idx + 8
    have nidx : idx.toNat = 16*k := by
      change (16*k) % 2^64 = 16*k
      exact Nat.mod_eq_of_lt (by omega)
    have naddr : addr.toNat = sp.toNat + 16*k + 8 := by
      change ((sp + idx) + 8).toNat = _
      simp only [BitVec.toNat_add,nidx,BitVec.reduceToNat,
        Nat.mod_eq_of_lt (show sp.toNat+16*k < 2^64 by omega),
        Nat.mod_eq_of_lt (show sp.toNat+16*k+8 < 2^64 by omega)]
    have indexNext : idx+16 = BitVec.ofNat 64 (16*(k+1)) := by
      change BitVec.ofNat 64 (16*k) + BitVec.ofNat 64 16 = _
      rw [←BitVec.ofNat_add]; congr 1
    have atEnd : len = idx + 16 ↔ k+1 = rem := by
      rw [indexNext]
      constructor
      · intro e
        have en := congrArg BitVec.toNat e
        change (16*rem)%2^64 = (16*(k+1))%2^64 at en
        rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at en
        omega
      · intro he; rw [he]
    have outStack := (stack.of_frame frame).of_frame aFrame
    have copyRead : Readable out.store (sp+152) 104 :=
      outStack.readable.sub (by omega) (by omega)
    have copyWrite : Writable code out.store addr 16 :=
      outStack.sub (by omega) (by omega)
    obtain ⟨next,runC,labC,iC,r9C,memC,keepC,typedC,cFrame⟩ :=
      tail_copy use256 code hcode out.arguments out.store sp idx len typA
        (congrArg (Value.get 64) ((keepA 4 (by decide)).trans r4))
        (congrArg (Value.get 64) ((keepA 13 (by decide)).trans r13))
        (congrArg (Value.get 64) ((keepA 12 (by decide)).trans ((keep 12 (by decide)).trans f12)))
        copyRead copyWrite
    change RamWriteFrame out.store next.store [span addr 16] at cFrame
    have reachC : (LIR.program.sem (dialect code)).Reaches ⟨out,[]⟩ ⟨next,[]⟩ := by
      have run : LIR.program.runBlock (dialect code) out = .jump next := by
        cases out with | mk l a m =>
          dsimp only at labA
          subst l
          exact runC
      apply Semantics.Reaches.single
      change LIR.program.step (dialect code) ⟨out,[]⟩ = .next ⟨next,[]⟩
      rw [Program.step,run]; rfl
    have labelC : next.label = (if k+1 = rem then (if use256 then .l109618 else .l108178)
        else (if use256 then .l1095b0 else .l108110)) := by
      simpa only [atEnd] using labC
    have savedA (p : BitVec 64) (lp : sp.toNat+216 ≤ p.toNat)
        (hp : p.toNat+8 ≤ sp.toNat+256) :
        memLoad out.store p 64 = memLoad loc.store p 64 := by
      apply aFrame.memLoad_eq
      change Outside _ p 8
      refine ⟨by omega, ?_⟩
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [span,s152,s256,cn] <;> change _ ∨ _ ≤ _ <;> omega
    have savedC (p : BitVec 64) (n : Nat) (hp : p.toNat+n ≤ 2^64)
        (apart : p.toNat+n ≤ addr.toNat ∨ addr.toNat+16 ≤ p.toNat) :
        Outside [span addr 16] p n := by
      refine ⟨hp,?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact apart
    have savedSlot (p : BitVec 64) (lp : sp.toNat+216 ≤ p.toNat)
        (hp : p.toNat+8 ≤ sp.toNat+256) :
        memLoad next.store p 64 = memLoad loc.store p 64 :=
      (cFrame.memLoad_eq (k:=64) (savedC p 8 (by omega) (by omega))).trans (savedA p lp hp)
    have nw : RamWriteFrame exit.store next.store work := by
      refine (frame.trans aFrame ?_).trans cFrame ?_
      · intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨span lower size,by simp [work],Nat.le_refl _,by change lower.toNat+room ≤ lower.toNat+size; omega⟩
        · refine ⟨span lower size,by simp [work],?_,?_⟩ <;> simp only [span,s152] <;> omega
        · refine ⟨span lower size,by simp [work],?_,?_⟩ <;> simp only [span,s256] <;> omega
        · exact ⟨span (counter+16) 4,by simp [work],Nat.le_refl _,Nat.le_refl _⟩
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨span lower size,by simp [work],?_,?_⟩ <;> simp only [span,naddr] <;> omega
    refine ⟨next,(reach.trans reachA).trans reachC,labelC,typedC,?_,?_,?_,
      (savedSlot _ (by omega) (by omega)).trans ds,(savedSlot _ (by omega) (by omega)).trans rs,
      (savedSlot _ (by omega) (by omega)).trans cslt,?_,nw,?_⟩
    · intro r hr
      have ha : r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] := by
        exact (by decide : ∀ r : Fin 53, r.val ∈ [3,4,5,12,14,15,22,39,50,51] →
          r.val ∈ [3,4,5,12,13,14,15,22,39,50,51]) r hr
      exact (keepC r hr).trans ((keepA r ha).trans (keep r hr))
    · exact r9C.trans (congrArg (Value.mk 64) ((savedA (sp+248) (by omega) (by omega)).trans cslt))
    · exact iC.trans (congrArg (Value.mk 64) indexNext)
    · have preserve := cFrame.memLoad_eq (k:=32) (savedC (counter+16) 4 (by omega) (by omega))
      rw [preserve,incA,val,BitVec.add_assoc]
      change _ + (BitVec.ofNat 32 (base+k) + BitVec.ofNat 32 1) = _
      rw [← BitVec.ofNat_add,Nat.add_assoc]
    · rw [memC]
      exact tail_keystream_copy loc.store out.store sp lower counter room k keyByte _
        low (by omega) (by omega) cs clim bytes aFrame
        (copyRead.sub (Nat.le_refl _) (by omega)) block cipherByte
  have done : ∀ k ≤ rem, P k := by
    intro k
    induction k with
    | zero => exact fun _ ↦ start
    | succ k ih => intro hk; exact advance k (by omega) (ih (by omega))
  obtain ⟨loc,reach,label,typed,keep,_,_,ds,rs,_,val,frame,bytes⟩ := done rem (Nat.le_refl _)
  rw [ite_eq_left rfl] at label
  rw [ncount] at val
  exact ⟨loc,reach,label,typed,preserved keep,
    congrArg (Value.get 64) ((keep 5 (by decide)).trans f5),
    ds,rs,val,frame,fun i hi ↦ bytes i (by omega)⟩

end AesGcm.Proofs.Machine.CTR
