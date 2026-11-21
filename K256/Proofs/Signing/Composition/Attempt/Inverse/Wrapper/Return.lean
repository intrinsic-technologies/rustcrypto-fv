import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper.State
import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Verify.Core.Serializer.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Verify.Core.Serializer (storeWords_wordsAt storeWords_frame)

private def returnWrites (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-89).toNat,1⟩, ⟨(p+8).toNat,33⟩]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
private theorem inverseReturnBlock {s : RamState} {b : Registers} {m : Ram} {k : Nat}
    (window : Writable Extracted.programImage m (sp s-96) 353)
    (room : 96 ≤ (sp s).toNat) (high : (sp s).toNat + 257 < 2^32)
    (regs : Unmasked s b k) (saved : Saved s m) :
    ∃ out : Output Value Ram Reg.count,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l109dcf,b,m⟩ = .returned out ∧
      out.tag = some ⟨64,0x105b0f⟩ ∧
      RegistersAt s out.values (sp s+624) (sp s+192) (sp s+656) (sp s+456) ∧
      WordsAt out.store (sp s+8) 64 (scalarWords (Curve.inverse domain.n k)) ∧
      memLoad out.store (sp s+40) 8 = 1 ∧ RamWriteFrame m out.store (returnWrites (sp s)) := by
  let p := sp s
  change 96 ≤ p.toNat at room
  change p.toNat + 257 < 2^32 at high
  let v := scalarWords (Curve.inverse domain.n k)
  let marked := memStore m (p-89) (1 : BitVec 8)
  let stored := memStore (memStore (memStore (memStore marked (p+8) v[0])
    (p+8+8) v[1]) (p+8+16) v[2]) (p+8+24) v[3]
  let result := memStore stored (p+40) (1 : BitVec 8)
  have mark : memLoad marked (p-89) 8 = 1 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have dstLow : (p+8).toNat + 32 ≤ 2^64 := by bv_omega
  have markedFrame : RamWriteFrame m marked (returnWrites p) := by
    refine (RamWriteFrame.refl _ _).memStore _ ⟨_,List.mem_cons_self,?_⟩
    change (p-89).toNat ≤ (p-89).toNat ∧ (p-89).toNat+1 ≤ (p-89).toNat+1 ∧ _
    exact ⟨Nat.le_refl _, Nat.le_refl _, by bv_omega⟩
  have storedFrame : RamWriteFrame m stored (returnWrites p) :=
    storeWords_frame v markedFrame
      ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,Nat.le_refl _,by change (p+8).toNat + 32 ≤ (p+8).toNat + 33; omega,dstLow⟩
  have resultFrame : RamWriteFrame m result (returnWrites p) := by
    refine storedFrame.memStore _ ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
    change (p+8).toNat ≤ (p+40).toNat ∧ (p+40).toNat+1 ≤ (p+8).toNat+33 ∧ _
    bv_omega
  have keep (i : BitVec 64) (lower : 8 ≤ i.toNat) (upper : i.toNat ≤ 48) :
      memLoad result (p-i) 64 = memLoad m (p-i) 64 := by
    apply resultFrame.memLoad_eq
    refine ⟨by bv_omega, fun r hr => ?_⟩
    simp only [returnWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (p-89).toNat+1 ≤ (p-i).toNat
      bv_omega
    · left
      change (p-i).toNat+8 ≤ (p+8).toNat
      bv_omega
  have back := (keep 8 (by decide) (by decide)).trans saved.ret
  have retLow : (0x105b0f : BitVec 64).toNat < 2^32 := by decide
  have stackM : Writable Extracted.programImage marked (p-96) 353 := window.memStore _ _
  have stackR : Writable Extracted.programImage result (p-96) 353 := window.of_frame resultFrame
  have anchor (i : BitVec 64) : p-i = p+(0-i) := by bv_omega
  have markWrite : Writable Extracted.programImage m (p-89) 1 :=
    window.of_offsets (anchor 89) (anchor 96) (by decide)
  have markRead := (markWrite.memStore (p-89) (1 : BitVec 8)).readable
  have pop (i : BitVec 64) (within : ((0-i)-(0-96)).toNat+8 ≤ 353) :
      LoadOk result (p-i) 8 := LoadOk.of_offsets stackR.readable (anchor i) (anchor 96) within
  have flagWrite : Writable Extracted.programImage stored (p+40) 1 :=
    (window.of_frame storedFrame).of_offsets (x := p) (c := 40) rfl (anchor 96) (by decide)
  have code : ∀ q ∈ codeRange 0x109dcf LIR.bytes_l109dcf, q ∈ Extracted.programImage :=
    fun q hq => Common.fnCode_subset_programImage q (LIR.code_l109dcf q hq)
  have rspBits : b[4].get 64 = p-96 := congrArg (Value.get 64) regs.rsp
  have dstBits : b[3].get 64 = p+8 := congrArg (Value.get 64) regs.rbx
  have r14 : b[14].get 64 = v[0] := congrArg (Value.get 64) regs.w0
  have r15 : b[15].get 64 = v[1] := congrArg (Value.get 64) regs.w1
  have r12 : b[12].get 64 = v[2] := congrArg (Value.get 64) regs.w2
  have r13 : b[13].get 64 = v[3] := congrArg (Value.get 64) regs.w3
  have zf : (!(testFlags (1 : BitVec 8)).ZF.getD false) = true := rfl
  have markEq : memStore m (p-89) (1 : BitVec 8) = marked := rfl
  have flag := regs.flag
  have flag64 : (b[0].get 64).setWidth 8 = 1 := by
    rw [Value.get, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide)]
    exact flag
  have addr (i : BitVec 64) : p-96+i = p-(96-i) := by bv_omega
  have sub (i j : BitVec 64) : p-i+j = p-(i-j) := by bv_omega
  have storedEq : memStore (memStore (memStore (memStore marked (p+8) v[0])
      (p+16) v[1]) (p+24) v[2]) (p+32) v[3] = stored := by
    simp only [stored, BitVec.add_assoc]
    rfl
  have resultEq : memStore stored (p+40) (1 : BitVec 8) = result := rfl
  refine ⟨?out,?run,?tag,?post,?words,?success,?frame⟩
  case run =>
    cfg_eval [LIR.b_l109dcf_1, rspBits, dstBits, flag64, addr, sub, BitVec.reduceSub,
      BitVec.add_assoc, BitVec.reduceAdd, markEq, mark, zf, r14, r15, r12, r13]
    simp only [storedEq, resultEq, back, retLow, and_true]
    refine Eq.trans (ite_eq_left (by slot_guard using code)) ?_
    refine Eq.trans (ite_eq_left (LoadOk.of_region markRead (Nat.le_refl _) (Nat.le_refl _))) ?_
    iterate 5 (refine Eq.trans (ite_eq_left (by slot_guard using code)) ?_)
    iterate 6 (refine Eq.trans (ite_eq_left (pop _ (by decide))) ?_)
    rfl
  case tag => rfl
  case post =>
    refine ⟨?_, regs.df, ?_, regs.rbp, ?_, ?_, ?_, ?_, ?_, regs.fp⟩
    · rfl
    · exact congrArg (Value.mk 64) ((keep 48 (by decide) (by decide)).trans saved.rbx)
    · exact congrArg (Value.mk 64) ((keep 40 (by decide) (by decide)).trans saved.r12)
    · exact congrArg (Value.mk 64) ((keep 32 (by decide) (by decide)).trans saved.r13)
    · rfl
    · exact congrArg (Value.mk 64) ((keep 16 (by decide) (by decide)).trans saved.r15)
    · intro ⟨i,_⟩ hi
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact regs.r9 | rfl
  case words =>
    have h := storeWords_wordsAt marked (p+8) v dstLow
    change WordsAt result (p+8) 64 v
    exact h.write_apart (p+40) (1 : BitVec 8) (by
      intro i hi j hj
      change i < 1 at hi
      change j < 32 at hj
      bv_omega)
  case success => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case frame => exact resultFrame

private theorem inverseSuccessBlock {s : RamState} {b : Registers} {m : Ram}
    (window : Writable Extracted.programImage m (sp s-96) 353)
    (regs : RegistersAt s b (sp s+624) (sp s+192) (sp s+656) (sp s+456))
    (flag : memLoad m (sp s+40) 8 = 1) :
    ∃ c, Reach (core .l105b0f b m) (core .l105b23 c (memStore m (sp s+256) (1 : BitVec 8))) ∧
      RegistersAt s c (sp s+624) (sp s+192) (sp s+656) (sp s+456) := by
  have rspBits : b[4].get 64 = sp s := congrArg (Value.get 64) regs.rsp
  have code : ∀ q ∈ codeRange 0x105b0f LIR.bytes_l105b0f, q ∈ Extracted.programImage :=
    fun q hq => Common.fnCode_subset_programImage q (LIR.code_l105b0f q hq)
  have run : ∃ c, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105b0f,b,m⟩ =
      .jump ⟨.l105b23,c,memStore m (sp s+256) (1 : BitVec 8)⟩ ∧
      RegistersAt s c (sp s+624) (sp s+192) (sp s+656) (sp s+456) := by
    refine ⟨?_,?step,?_⟩
    case step =>
      cfg_eval [rspBits, flag]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code)
      rfl
    refine ⟨regs.rsp, regs.df, regs.rbx, regs.rbp, regs.r12, regs.r13, regs.r14, regs.r15, ?_, regs.fp⟩
    intro ⟨i, bound⟩ hi
    have width := regs.widths ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact width
  obtain ⟨c,run,next⟩ := run
  refine ⟨c,.single ?_,next⟩
  change (LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105b0f,b,m⟩).next
    (dialect Extracted.programImage) [resume .l102795 0x102795] = _
  rw [run]
  rfl

theorem returnInverse {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a b : Registers} {m n : Ram} {st : State} {k : Nat}
    (reduced : DigestReduced s d msg st k a m) (regs : Unmasked s b k) (saved : Saved s n)
    (writes : RamWriteFrame m n (inverseRegion s)) :
    ∃ c t, Reach (wrapped .l109dcf b n) (core .l105b23 c t) ∧ ScalarsReady s d msg st k c t := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have window : Writable Extracted.programImage n (sp s-96) 353 := by
    rw [show sp s-96 = sp s+(0-96) by bv_omega]
    exact (stackWindow call reduced.toMemory (by decide)).of_frame writes
  obtain ⟨out,run,ret,restored,inverse,flag,frame⟩ :=
    inverseReturnBlock window (by omega) (by omega) regs saved
  have resumePath : Reach (wrapped .l109dcf b n) (core .l105b0f out.values out.store) := by
    refine .single ?_
    change (LIR.program.runBlock (dialect Extracted.programImage) ⟨.l109dcf,b,n⟩).next
      (dialect Extracted.programImage) wrapperStack = _
    rw [run]
    have loc : (resume .l105b0f 0x105b0f).resume out =
        (⟨.l105b0f,out.values,out.store⟩ : LIR.lifted.Location) :=
      congrArg (fun args => (⟨.l105b0f,args,out.store⟩ : LIR.lifted.Location))
        (ParseSignature.resume_arguments (resume .l105b0f 0x105b0f) out)
    have accepts : (resume .l105b0f 0x105b0f).Accepts (dialect Extracted.programImage) out.tag = true := by
      rw [ret]
      rfl
    simp only [Transfer.next, accepts, ↓reduceIte, loc]
    rfl
  obtain ⟨c,path,ready⟩ := inverseSuccessBlock (window.of_frame frame) restored flag
  have before : RamWriteFrame m out.store (inverseRegion s) := by
    apply writes.trans frame
    intro r hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [returnWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change (sp s-840).toNat ≤ (sp s-89).toNat ∧ (sp s-89).toNat+1 ≤ (sp s-840).toNat+1104
      bv_omega
    · change (sp s-840).toNat ≤ (sp s+8).toNat ∧ (sp s+8).toNat+33 ≤ (sp s-840).toNat+1104
      bv_omega
  let t := memStore out.store (sp s+256) (1 : BitVec 8)
  have after : RamWriteFrame m t (inverseRegion s) := by
    refine before.memStore _ ⟨_,List.mem_singleton_self _,?_⟩
    change (sp s-840).toNat ≤ (sp s+256).toNat ∧ (sp s+256).toNat+1 ≤ (sp s-840).toNat+1104 ∧ _
    bv_omega
  have work : RamWriteFrame m t (workRegions s) := by
    apply (RamWriteFrame.refl m (workRegions s)).trans after
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_⟩
    change (sp s-9904).toNat ≤ (sp s-840).toNat ∧ (sp s-840).toNat+1104 ≤ (sp s-9904).toNat+10248
    bv_omega
  have outside (i : BitVec 64) (lower : 624 ≤ i.toNat) (upper : i.toNat ≤ 656) :
      Outside (inverseRegion s) (sp s+i) 32 := by
    refine ⟨by bv_omega,fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (sp s-840).toNat + 1104 ≤ (sp s+i).toNat
    bv_omega
  refine ⟨c,t,resumePath.trans path,⟨reduced.toLoopMemory.preserve_work call work,ready,
    WordsAt.of_frame reduced.nonce after (by decide) (outside 624 (by decide) (by decide)),
    WordsAt.of_frame reduced.digest after (by decide) (outside 656 (by decide) (by decide)),?_⟩⟩
  apply inverse.write_apart
  intro i hi j hj
  change i < 1 at hi
  change j < 32 at hj
  bv_omega

end K256.Proofs.Signing.Composition.Attempt.Inverse
