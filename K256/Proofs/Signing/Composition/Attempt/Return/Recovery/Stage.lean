import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.State
import K256.Proofs.Signing.Nonce.Start.Prepare.Scalar
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Memory
import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Transfer.Verify

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

private def copied (m : Ram) (p : BitVec 64) : Ram :=
  let s₀ := memStore m (p+248) (memLoad m (p+72) 64)
  let s₁ := memStore s₀ (p+240) (memLoad m (p+64) 64)
  let s₂ := memStore s₁ (p+232) (memLoad m (p+56) 64)
  let s₃ := memStore s₂ (p+224) (memLoad m (p+48) 64)
  let r₀ := memStore s₃ (p+216) (memLoad m (p+40) 64)
  let r₁ := memStore r₀ (p+208) (memLoad m (p+32) 64)
  let r₂ := memStore r₁ (p+192) (memLoad m (p+16) 64)
  memStore r₂ (p+200) (memLoad m (p+24) 64)

private def preservedRegs : List Nat := [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51]

private theorem successBranch {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4] = ⟨64,p⟩) (win : Readable m p 80)
    (tag : memLoad m (p+8) 8 = 0) :
    ∃ b : Registers,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105d35,a,m⟩ = .jump ⟨.l105d62,b,m⟩ ∧
      b[4] = ⟨64,p⟩ ∧ b[7] = ⟨64,memLoad m (p+16) 64⟩ ∧
      b[0] = ⟨64,memLoad m (p+24) 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ preservedRegs → b[i] = a[i]) := by
  have bits : a[4].get 64 = p := congrArg (Value.get 64) rsp
  have h8 : LoadOk m (p+8) 1 := LoadOk.of_offsets win rfl (BitVec.add_zero _).symm (by decide)
  have h16 : LoadOk m (p+16) 8 := LoadOk.of_offsets win rfl (BitVec.add_zero _).symm (by decide)
  have h24 : LoadOk m (p+24) 8 := LoadOk.of_offsets win rfl (BitVec.add_zero _).symm (by decide)
  refine ⟨?_,?run,?_⟩
  case run =>
    cfg_eval [bits,h8,h16,h24,tag]
    rfl
  refine ⟨rsp,rfl,rfl,?_⟩
  intro ⟨i,hi⟩ member
  simp only [preservedRegs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxHeartbeats 1200000 in
private theorem serializerCall {b : Registers} {m : Ram} {p : BitVec 64}
    (rsp : b[4] = ⟨64,p⟩) (rdi : b[7] = ⟨64,memLoad m (p+16) 64⟩)
    (rax : b[0] = ⟨64,memLoad m (p+24) 64⟩)
    (win : Writable Extracted.programImage m (p-8) 264) :
    ∃ c : Registers,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105d62,b,m⟩ =
        .call ⟨.l109e30,c,memStore (copied m p) (p-8) (0x105dd5 : BitVec 64)⟩
          (resume .l105dd5 0x105dd5) ∧
      c[4].get 64 = p-8 ∧ c[6].get 64 = p+128 ∧ c[7].get 64 = p+160 ∧
      (∀ i : Fin Reg.count, i.val ∈ preservedRegs → c[i] = b[i]) := by
  have bits : b[4].get 64 = p := congrArg (Value.get 64) rsp
  have first : b[7].get 64 = memLoad m (p+16) 64 := congrArg (Value.get 64) rdi
  have next : b[0].get 64 = memLoad m (p+24) 64 := congrArg (Value.get 64) rax
  refine ⟨?_,?run,?_⟩
  case run =>
    cfg_eval [bits,first,next]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using LIR.code_l105d62)
    simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
    rfl
  refine ⟨rfl,rfl,rfl,?_⟩
  intro ⟨i,hi⟩ member
  simp only [preservedRegs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem return_without_guard {p : Prop} [Decidable p]
    {t : Transfer Value Ram Verify.LIR.Label signature Reg.count} {out : Output Value Ram Reg.count}
    (eq : (if p then t else .stuck) = .returned out) : t = .returned out := by
  split at eq <;> first | exact eq | cases eq

set_option maxHeartbeats 900000 in
private theorem serializerArgs {code : CodeMap} {c : Registers} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Verify.LIR.program.runBlock (dialect code) ⟨.l109e30,c,m⟩ = .returned out)
    (w8 : c[8].width = 64) (w9 : c[9].width = 64) :
    ParseSignature.ArgumentWidths out.values := by
  cfg_eval at run
  repeat' replace run := return_without_guard run
  cases run
  intro ⟨i,hi⟩ member
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact w8 | exact w9 | rfl


open Generate.Generator.Multiply (scalarWords)
open Generate.Wrapper (writeScalarWords)

private theorem wordAtOffset (p : BitVec 64) (k i : Nat) :
    wordAddr (p+BitVec.ofNat 64 k) 64 i = p+BitVec.ofNat 64 (k+8*i) := by
  rw [wordAddr, BitVec.add_assoc, BitVec.ofNat_add]

private theorem copiedWords {m : Ram} {p : BitVec 64} {r sigS : Nat}
    (first : WordsAt m (p+16) 64 (scalarWords r))
    (second : WordsAt m (p+48) 64 (scalarWords sigS)) :
    WordsAt (memStore (copied m p) (p-8) (0x105dd5 : BitVec 64)) (p+192) 64 (scalarWords r) ∧
    WordsAt (memStore (copied m p) (p-8) (0x105dd5 : BitVec 64)) (p+224) 64 (scalarWords sigS) := by
  constructor <;> intro i hi
  · refine Eq.trans ?_ (first i hi)
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals simp (disch := first | decide | store_disch) only [wordAddr,Nat.reduceDiv,Nat.reduceMul,
      reduceAddOffset,BitVec.add_zero,copied,memLoad_memStore_same,memLoad_memStore_of_rangeApart]
  · refine Eq.trans ?_ (second i hi)
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals simp (disch := first | decide | store_disch) only [wordAddr,Nat.reduceDiv,Nat.reduceMul,
      reduceAddOffset,BitVec.add_zero,copied,memLoad_memStore_same,memLoad_memStore_of_rangeApart]

private theorem serializerFrame {regions : List MemoryRegion} {p : BitVec 64}
    {word : Nat → BitVec 64} {m : Ram} (count : Nat)
    (within : ∀ i < count, InRegions regions (wordAddr p 64 i) 8) :
    RamWriteFrame m (writeScalarWords p word m count) regions := by
  induction count with
  | zero => exact .refl _ _
  | succ n ih => exact (ih fun i hi => within i (by omega)).memStore _ (within n (by omega))

set_option maxHeartbeats 900000 in
theorem stage {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {r sigS : Nat}
    (input : Constructed s d msg st r sigS a m) (nz : ¬ (r = 0 ∨ sigS = 0)) :
    ∃ b n, Reach (core .l105d35 a m) (core .l105dd5 b n) ∧ Staged s d r sigS b n := by
  let p := sp s
  let t := memStore (copied m p) (p-8) (0x105dd5 : BitVec 64)
  let scratch : MemoryRegion := ⟨(p-8).toNat,264⟩
  let serialized : MemoryRegion := ⟨(p+160).toNat,32⟩
  let word (i : Nat) := bswapSpec (memLoad t (wordAddr (p+128) 64 (3-i)) 64)
  let encoded := writeScalarWords (p+160) word t
  obtain ⟨room,high,base⟩ := stackBounds call
  change p.toNat = (stackPtr s).toNat-1288 at base
  have slotNat : (p-8).toNat = p.toNat-8 := belowNat call (by decide)
  have offset (i : Nat) (hi : i ≤ 256) : (p+BitVec.ofNat 64 i).toNat = p.toNat+i :=
    offsetNat call (by omega)
  have srcAddr (i : Nat) : wordAddr (p+128) 64 i = p+BitVec.ofNat 64 (128+8*i) :=
    wordAtOffset p 128 i
  have dstAddr (i : Nat) : wordAddr (p+160) 64 i = p+BitVec.ofNat 64 (160+8*i) :=
    wordAtOffset p 160 i
  have inCopy (i : Nat) (hi : i+8 ≤ 256) : InRegions [scratch] (p+BitVec.ofNat 64 i) 8 := by
    refine ⟨scratch,List.mem_singleton_self _,?_⟩
    change (p-8).toNat ≤ _ ∧ _ + 8 ≤ (p-8).toNat+264 ∧ _ + 8 ≤ 2^64
    rw [slotNat,offset i (by omega)]
    omega
  have inSlot : InRegions [scratch] (p-8) 8 := by
    refine ⟨scratch,List.mem_singleton_self _,?_⟩
    change (p-8).toNat ≤ (p-8).toNat ∧ (p-8).toNat+8 ≤ (p-8).toNat+264 ∧ (p-8).toNat+8 ≤ 2^64
    rw [slotNat]
    omega
  have copyFrame : RamWriteFrame m t [scratch] :=
    (((((((((RamWriteFrame.refl m _).memStore _ (inCopy 248 (by decide))).memStore _
      (inCopy 240 (by decide))).memStore _ (inCopy 232 (by decide))).memStore _
      (inCopy 224 (by decide))).memStore _ (inCopy 216 (by decide))).memStore _
      (inCopy 208 (by decide))).memStore _ (inCopy 192 (by decide))).memStore _
      (inCopy 200 (by decide))).memStore _ inSlot
  have serializedNat : (p+160).toNat = p.toNat+160 := offset 160 (by decide)
  have intoBuffer (count : Nat) (hc : count ≤ 4) : RamWriteFrame t (encoded count) [serialized] := by
    apply serializerFrame
    intro i hi
    refine ⟨serialized,List.mem_singleton_self _,?_⟩
    rw [dstAddr,InRegion,offset _ (by omega)]
    change (p+160).toNat ≤ _ ∧ _ ≤ (p+160).toNat+32 ∧ _
    rw [serializedNat]
    omega
  have bufferInside : RegionsWithin [serialized] [scratch] := by
    intro reg member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨scratch,List.mem_singleton_self _,?_⟩
    change (p-8).toNat ≤ (p+160).toNat ∧ (p+160).toNat+32 ≤ (p-8).toNat+264
    rw [slotNat,serializedNat]
    omega
  have safe : CoreMemory s d (encoded 4) :=
    preserveCore call input.toCoreMemory (copyFrame.trans (intoBuffer 4 (by decide)) bufferInside) (by
      intro reg member
      obtain rfl := List.mem_singleton.mp member
      change _ ≤ (p-8).toNat ∧ (p-8).toNat+264 ≤ _
      rw [slotNat]
      change p.toNat-9904 ≤ p.toNat-8 ∧ p.toNat-8+264 ≤ p.toNat+344
      omega)
  have readConstructor : Readable m p 80 := by
    have h := (stackWindow (offset := 0) (size := 80) call input.toMemory (by decide)).readable
    change Readable m (sp s + 0#64) 80 at h
    rw [BitVec.add_zero] at h
    exact h
  have result := input.output
  rw [ite_eq_right nz] at result
  obtain ⟨tag,first,second⟩ := result
  obtain ⟨b,branch,bsp,bdi,bax,bkeep⟩ := successBranch input.rsp readConstructor tag
  have frame : Writable Extracted.programImage m (p-8) 264 := by
    rw [addr_sub]
    exact stackWindow call input.toMemory (by decide)
  obtain ⟨c,push,csp,csi,cdi,ckeep⟩ := serializerCall bsp bdi bax frame
  have load (i : Nat) (hi : i < 4) : LoadOk t (wordAddr (p+128) 64 i) 8 := by
    rw [srcAddr]
    apply LoadOk.of_region (frame.readable.of_frame copyFrame)
      (by rw [slotNat, offset _ (by omega)]; omega)
      (by rw [slotNat, offset _ (by omega)]; omega)
  have dstWritable (i : Nat) (hi : i < 4) :
      Writable Extracted.programImage (encoded i) (wordAddr (p+160) 64 i) 8 := by
    rw [dstAddr]
    apply ((frame.of_frame copyFrame).of_frame (intoBuffer i (by omega))).sub
      (by rw [slotNat, offset _ (by omega)]; omega)
      (by rw [slotNat, offset _ (by omega)]; omega)
  have stores (i off len : Nat) (hi : i < 4) (inCode : off+len ≤ Verify.LIR.bytes_l109e30.length) :
      StoreOk Extracted.programImage (encoded i) (wordAddr (p+160) 64 i) 8
        (0x109e30+BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange (dstWritable i hi)
      (fun x hx => Common.fnCode_subset_programImage x (Verify.LIR.code_l109e30 x hx)) inCode
  have retOk : LoadOk (encoded 4) (p-8) 8 :=
    let rd := ((frame.readable.of_frame copyFrame).of_frame (intoBuffer 4 (by decide))).sub
      (Nat.le_refl _) (by omega)
    ⟨rd.low,rd.present⟩
  have ret : memLoad (encoded 4) (p-8) 64 = 0x105dd5 := by
    rw [(intoBuffer 4 (by decide)).memLoad_eq (a := p-8) (k := 64)]
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · refine ⟨by rw [slotNat]; omega,fun reg member => ?_⟩
      obtain rfl := List.mem_singleton.mp member
      left
      change (p-8).toNat + 8 ≤ (p+160).toNat
      rw [slotNat,serializedNat]
      omega
  obtain ⟨out,run,outTag,outMem,outSp,outKeep⟩ := Signing.Nonce.Start.serializeScalarBlock
    csp csi cdi load (fun _ _ => rfl)
    (by
      have h := stores 0 30 3 (by decide) (by decide)
      rw [show wordAddr (p+160) 64 0 = p+160 from BitVec.add_zero _] at h
      exact h)
    (stores 1 33 4 (by decide) (by decide)) (stores 2 37 4 (by decide) (by decide))
    (stores 3 41 4 (by decide) (by decide)) retOk ret (by decide)
  have exec : Verify.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l109e30,c,t⟩,[]⟩ out :=
    .done (by simp only [Program.step,run,Transfer.next])
  have transferred := Signing.Transfer.verifyExecAt (src := .l109e30) (dst := .l109e30) rfl exec
  have reach : Reach (core .l105d35 a m) (core .l105dd5 out.values out.store) :=
    .step (congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) branch)
      (callReaches push transferred outTag)
  have kept (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[i] = a[i] := by
    refine (outKeep i h).trans ((ckeep i ?_).trans (bkeep i ?_))
    all_goals simp only [preservedRegs,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    all_goals omega
  have saved (i : Fin Reg.count) (h : i.val ∈ Activation.calleeSavedNumbers) :
      out.values[i].width = 64 := by
    rw [kept i (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)]
    obtain ⟨i,hi⟩ := i
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width input.rbx
    · exact congrArg Value.width input.rbp
    · exact congrArg Value.width input.r12
    · exact congrArg Value.width input.r13
    · exact input.r14
    · exact congrArg Value.width input.r15
  have args := serializerArgs run
    ((congrArg Value.width ((ckeep 8 (by decide)).trans (bkeep 8 (by decide)))).trans (input.widths 8 (by decide)))
    ((congrArg Value.width ((ckeep 9 (by decide)).trans (bkeep 9 (by decide)))).trans (input.widths 9 (by decide)))
  obtain ⟨stagedR,stagedS⟩ := copiedWords first second
  have apart (i : Nat) (lo : 192 ≤ i) (hi : i ≤ 224) :
      Outside [serialized] (p+BitVec.ofNat 64 i) 32 := by
    rw [Outside,offset i (by omega)]
    refine ⟨by omega,fun reg member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    right
    change (p+160).toNat+32 ≤ p.toNat+i
    rw [serializedNat]
    omega
  have spEq : p-8+8 = p := BitVec.sub_add_cancel _ _
  have popped : out.values[4] = ⟨64,sp s⟩ := by
    change out.values[4] = ⟨64,p-8+8⟩ at outSp
    rwa [spEq] at outSp
  rw [outMem] at reach
  exact ⟨_,_,reach,safe,popped,(kept 22 (by decide)).trans input.df,saved,args,
    ⟨(congrArg Value.width (kept 39 (by decide))).trans input.fp.1,
     (congrArg Value.width (kept 50 (by decide))).trans input.fp.2.1,
     (congrArg Value.width (kept 51 (by decide))).trans input.fp.2.2⟩,
    stagedR.of_frame (intoBuffer 4 (by decide)) (by decide) (apart 192 (by decide) (by decide)),
    stagedS.of_frame (intoBuffer 4 (by decide)) (by decide) (apart 224 (by decide) (by decide))⟩

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
