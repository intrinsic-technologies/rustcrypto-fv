import K256.Proofs.Verify.Wrapper.State
import K256.Proofs.Verify.Wrapper.Copy.Prepare
import K256.Proofs.Verify.Transfer.Signature

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.NIST.SHA2

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

private theorem narrow_zero {n : Ram} {ptr : BitVec 64} (z : memLoad n ptr 64 = 0)
    (w : Nat) (aligned : w % 8 = 0) (fits : w ≤ 64) : memLoad n ptr w = 0 := by
  have h := extractLsb'_memLoad n ptr (n := 64) 0 w (by decide) aligned (by omega)
  rw [z, Nat.zero_div, BitVec.add_zero] at h
  exact h.symm.trans (by apply BitVec.eq_of_toNat_eq; simp)

private theorem signatureParser {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point}
    {r s : Nat} (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (decoded : Ecdsa.signatureScalars sig = some (r,s))
    (fr : Activation) (a : Core.Registers)
    (entry : Atom.All Extracted.programImage a fr.original (Fn103ac0.frameAt .l103ac0 fr))
    (memory : Memory initial fr.original) (si : fr.rsi = initial.regValue .rcx)
    (di : fr.rdi = stackPtr initial - 528)
    (top : fr.rsp.toNat = (stackPtr initial).toNat - 544)
    (floor : fr.low.toNat = (stackPtr initial).toNat - 1104)
    (point : Ecdh.Decode.AffinePointAt fr.original (localSp initial + 416) p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l103ac0,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn103ac0.doneAt fr) ∧
      Memory initial out.store ∧ AffineInputs initial out.store p r s 16 ∧ memLoad out.store fr.rdi 64 = 0 := by
  obtain ⟨depth,lim⟩ := Verify.Hash.Update.stackBounds call
  have dest : fr.rdi.toNat = (stackPtr initial).toNat - 528 := by
    rw [di]
    exact Common.stackOffset call.stackAvailable (by decide)
  have bytes := (inputMemory call memory.frame).2.2.1
  have input : ValidInput initial (registerRegion initial .rcx 64) sig := call.inputsInMemory.2.2.1
  have readable := Readable.of_hasBytes bytes input.2.1
  have len : sig.size = 64 := bytes.1
  rw [len] at readable
  have rd : Readable fr.original fr.rsi 64 := by
    rw [si]
    change Readable _ (BitVec.ofNat 64 (initial.regValue .rcx).toNat) 64 at readable
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using readable
  have sep : MemorySeparation [stack initial] [registerRegion initial .rdi 65,
      registerRegion initial .rsi msg.size, registerRegion initial .rcx 64] := call.separation
  have pos : 0 < (stack initial).size := by
    change 0 < (stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 13000)
    omega
  have apart := apart_of_disjoint ((sep.2 _ List.mem_cons_self).2 _ (by simp : registerRegion initial .rcx 64 ∈ _))
    pos (show 0 < 64 by decide)
  change (stackPtr initial).toNat - 13000 + ((stackPtr initial).toNat+8-((stackPtr initial).toNat-13000))
    ≤ (initial.regValue .rcx).toNat ∨ (initial.regValue .rcx).toNat + 64 ≤ (stackPtr initial).toNat - 13000 at apart
  have srcApart : Outside [ParseSignature.callStack fr] fr.rsi 64 := by
    refine ⟨by have := rd.low; omega, ?_⟩
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    change fr.rsi.toNat + 64 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat
    rw [si]
    omega
  have dstApart : Outside [ParseSignature.callStack fr] fr.rdi 72 := by
    refine ⟨by omega, ?_⟩
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    apply Or.inr
    change fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat
    omega
  have wr := (Common.stackWritable (off := 528) (len := 72) call (by decide) (by decide) (by decide)).of_frame memory.frame
  obtain ⟨out,run,ret,done_,writes,_,flag,hr,hs⟩ := Verify.Transfer.signatureExecution fr a entry rd
    (di ▸ wr) srcApart dstApart (by rw [si]; exact bytes) decoded
  have bounds : ∀ reg ∈ [fr.region, ⟨fr.rdi.toNat,72⟩], (stackPtr initial).toNat - 13000 ≤ reg.start ∧
      reg.start + reg.size ≤ (stackPtr initial).toNat - 456 := by
    intro reg h
    rcases List.mem_cons.mp h with h | h
    · subst reg
      change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp h
      change _ ≤ fr.rdi.toNat ∧ fr.rdi.toNat + 72 ≤ _
      omega
  refine ⟨out,run,ret,done_,memory.advance call writes (fun reg h => ⟨(bounds reg h).1,
    Nat.le_trans (bounds reg h).2 (by omega)⟩), ⟨point.of_copy ?_, ?_, ?_⟩,flag⟩
  · intro off width fits
    apply writes.memLoad_eq
    have base : localSp initial + 416 = stackPtr initial - 120 := by unfold localSp; bv_omega
    rw [base]
    have bn : (stackPtr initial - 120).toNat = (stackPtr initial).toNat - 120 :=
      Common.stackOffset call.stackAvailable (by decide)
    have addr : (stackPtr initial - 120 + BitVec.ofNat 64 off).toNat = (stackPtr initial).toNat - 120 + off := by
      rw [BitVec.toNat_add, bn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, fun reg h => Or.inr (by have := (bounds reg h).2; omega)⟩
  · rw [di] at hr
    rwa [show stackPtr initial - 528 + 8 = localSp initial + 16 by unfold localSp; bv_omega] at hr
  · rw [di] at hs
    rwa [show stackPtr initial - 528 + 40 = localSp initial + (16 + 32) by unfold localSp; bv_omega] at hs

private theorem parserSaved (i : RamState) :
    let a := parserRegisters i
    a[5] = (Reg.ofIndex 5).read i ∧ a[13] = (Reg.ofIndex 13).read i ∧
    a[3] = ⟨64,i.regValue .rdx⟩ ∧ a[14] = ⟨64,i.regValue .rsi⟩ ∧
    a[15] = ⟨64,i.regValue .rcx⟩ := by
  dsimp only
  simp only [parserRegisters, parserArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte,
    Lifted.locationOf, Vector.getElem_ofFn, true_and]

private theorem savedValues (i : RamState) (m : Ram) (a : Vector Value 53) (window : Nat) (ret : BitVec 64)
    (saved : a[5] = (Reg.ofIndex 5).read i ∧ a[13] = (Reg.ofIndex 13).read i ∧
      a[3] = ⟨64,i.regValue .rdx⟩ ∧ a[14] = ⟨64,i.regValue .rsi⟩ ∧ a[15] = ⟨64,i.regValue .rcx⟩) :
    let fr := childActivation i m a window ret
    Value.mk 64 fr.rbp = (Reg.ofIndex 5).read i ∧ Value.mk 64 fr.r13 = (Reg.ofIndex 13).read i ∧
    fr.rbx = i.regValue .rdx ∧ fr.r14 = i.regValue .rsi ∧ fr.r15 = i.regValue .rcx := by
  obtain ⟨bp,r13,bx,r14,r15⟩ := saved
  change Value.mk 64 (a[5].get 64) = _ ∧ Value.mk 64 (a[13].get 64) = _ ∧
    a[3].get 64 = _ ∧ a[14].get 64 = _ ∧ a[15].get 64 = _
  rw [bp,r13,bx,r14,r15]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

private abbrev signatureRegs (initial : RamState) (a : Core.Registers) :=
  signatureCallArgs (a.set 19 (.ofBool true)) (localSp initial)

local macro "signature_regs" : tactic =>
  `(tactic| simp only [signatureRegs, signatureCallArgs, Fin.getElem_fin,
    Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte])

set_option maxHeartbeats 340000 in
theorem parseSignature (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (decoded : Ecdsa.signatureScalars sig = some (r,s))
    (atoms : Atom.All Extracted.programImage a m (Fn106390.doneAt (parserActivation initial)))
    (memory : Memory initial m) (widths : ParseSignature.ArgumentWidths a)
    (tag : memLoad m (stackPtr initial - 528) 64 = 0)
    (point : Ecdh.Decode.AffinePointAt m (stackPtr initial - 528 + 8) p) :
    ∃ b t, Core.Reaches .l102fe9 a m .l103037 b t ∧ HashInput initial b t p r s := by
  let sp := localSp initial
  let afterKey := a.set 19 (.ofBool true)
  let b := signatureRegs initial a
  let pushed := memStore (copiedKey m sp) (sp - 8) (0x10302c : BitVec 64)
  let fr := childActivation initial pushed b 560 0x10302c
  have slot : sp - 8 = stackPtr initial - 544 := by dsimp only [sp, localSp]; bv_omega
  have dst : sp + 8 = stackPtr initial - 528 := by dsimp only [sp, localSp]; bv_omega
  have stack : (stackPtr initial - 544) + 8 = sp := by dsimp only [sp,localSp]; bv_omega
  simp only [Fn106390.doneAt, Atom.All, Atom.Holds, Fin.getElem_fin] at atoms
  obtain ⟨rsp,df,bx,bp,r12,r13,r14,r15,mx,ftw,fcw,_⟩ := atoms
  change a[4] = ⟨64, stackPtr initial - 544 + 8⟩ at rsp
  rw [stack] at rsp
  obtain ⟨p5,p13,p3,p14,p15⟩ :=
    savedValues initial (parserMemory initial) (parserRegisters initial) 1544 0x102fe9 (parserSaved initial)
  have parseRbp : a[5] = (Reg.ofIndex 5).read initial := bp.trans p5
  have parseR13 : a[13] = (Reg.ofIndex 13).read initial := r13.trans p13
  have parseLen : a[3] = ⟨64, initial.regValue .rdx⟩ := bx.trans (congrArg (Value.mk 64) p3)
  have parseMsg : a[14] = ⟨64, initial.regValue .rsi⟩ := r14.trans (congrArg (Value.mk 64) p14)
  have parseSig : a[15] = ⟨64, initial.regValue .rcx⟩ := r15.trans (congrArg (Value.mk 64) p15)
  have loadTag {n : Ram} (mem : Memory initial n) (size : Nat) (fits : size ≤ 72)
      (pos : 0 < size) : LoadOk n (sp+8) size := by
    rw [dst]
    have rd := ((Common.stackWritable (off := 528) (len := size) call (by decide) (by omega) pos).of_frame
      mem.frame).readable
    exact ⟨rd.low, rd.present⟩
  have keyBlock := keyTag (code := Extracted.programImage) (sp := sp) (congrArg (Value.get 64) rsp)
    (loadTag memory 1 (by decide) (by decide))
  have keyFlag : memLoad m (sp + 8) 8 = 0 := dst ▸ narrow_zero tag 8 (by decide) (by decide)
  dsimp only at keyBlock
  rw [show (memLoad m (sp + 8) 8 == 0) = true by rw [keyFlag]; rfl] at keyBlock
  have keyPath : Core.Reaches .l102fe9 a m .l102ff4 afterKey m :=
    .single (by change (program.runBlock _ _).next _ _ = _; rw [keyBlock]; rfl)
  have sp' : afterKey[4].get 64 = sp := by
    simp only [afterKey, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.get 64) rsp
  have df' : afterKey[22].get 1 = 0 := by
    simp only [afterKey, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.get 1) df
  have point' : Ecdh.Decode.AffinePointAt m (sp + 16) p := by
    rwa [show sp + 16 = stackPtr initial - 528 + 8 by rw [← dst, BitVec.add_assoc]; rfl]
  obtain ⟨block, mem, copied, ret⟩ := prepareSignature call memory sp' df' point'
  have regs : ChildRegisters initial b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [b]; signature_regs
      exact congrArg (Value.mk 64) slot
    · simp only [b]; signature_regs; exact df
    · rintro ⟨j,hj⟩ hj'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj'
      rcases hj' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [b] <;> signature_regs <;> first
        | rfl
        | exact congrArg Value.width bx
        | exact congrArg Value.width bp
        | exact congrArg Value.width r12
        | exact congrArg Value.width r13
        | exact congrArg Value.width r14
        | exact congrArg Value.width r15
        | exact widths 1 (by decide)
        | exact widths 2 (by decide)
        | exact widths 8 (by decide)
        | exact widths 9 (by decide)
    all_goals
      simp only [b]
      signature_regs
      first
        | exact congrArg Value.width mx
        | exact congrArg Value.width ftw
        | exact congrArg Value.width fcw
  have entryAtoms : Atom.All Extracted.programImage b pushed (Fn103ac0.frameAt .l103ac0 fr) := by
    change Atom.All _ b pushed (Fn103ac0.frameInfo.entryAtoms fr)
    exact childEntry call mem regs Fn103ac0.frameInfo (room := 560) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide) (slot ▸ ret)
  have srcReg : b[6] = ⟨64, a[15].get 64⟩ := by simp only [b]; signature_regs
  have dstReg : b[7] = ⟨64, sp + 8⟩ := by simp only [b]; signature_regs; rfl
  have si : fr.rsi = initial.regValue .rcx := by
    change b[6].get 64 = _
    rw [srcReg,parseSig]
    rfl
  have di : fr.rdi = stackPtr initial - 528 := (congrArg (Value.get 64) dstReg).trans dst
  obtain ⟨out,run,ret',done_,outMem,operands,flag⟩ := signatureParser call decoded fr b entryAtoms mem si di
    (Common.stackOffset (off := 544) call.stackAvailable (by decide))
    (Common.stackOffset (off := 1104) call.stackAvailable (by decide)) copied
  have callPath := Verify.reachesOfCall (resume := .l10302c) block run ret'
  simp only [Fn103ac0.doneAt, Atom.All, Atom.Holds, Fin.getElem_fin] at done_
  obtain ⟨rsp₂,df₂,bx₂,bp₂,r12₂,r13₂,r14₂,_,mx₂,ftw₂,fcw₂,_⟩ := done_
  change out.values[4] = ⟨64,stackPtr initial - 544 + 8⟩ at rsp₂
  rw [stack] at rsp₂
  have sigBlock := signatureTag (code := Extracted.programImage) (sp := sp) (congrArg (Value.get 64) rsp₂)
    (loadTag outMem 4 (by decide) (by decide))
  have sigFlag : memLoad out.store (sp + 8) 32 = 0 := by
    rw [dst, ← di]
    exact narrow_zero flag 32 (by decide) (by decide)
  dsimp only at sigBlock
  rw [show (memLoad out.store (sp + 8) 32 == 1) = false by rw [sigFlag]; rfl] at sigBlock
  let c := out.values.set 19 (.ofBool false)
  have endPath : Core.Reaches .l10302c out.values out.store .l103037 c out.store :=
    .single (by change (program.runBlock _ _).next _ _ = _; rw [sigBlock]; rfl)
  refine ⟨c, out.store, keyPath.trans (callPath.trans endPath), ⟨⟨outMem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    operands, ?_, ?_⟩⟩
  all_goals simp only [c,Vector.getElem_set,Nat.reduceEqDiff,↓reduceIte]
  · exact rsp₂
  · have kept : b[5] = a[5] := by simp only [b]; signature_regs
    exact bp₂.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) (kept.trans parseRbp))
  · have kept : b[13] = a[13] := by simp only [b]; signature_regs
    exact r13₂.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) (kept.trans parseR13))
  · exact df₂
  · exact congrArg Value.width r12₂
  · exact congrArg Value.width mx₂
  · exact congrArg Value.width ftw₂
  · exact congrArg Value.width fcw₂
  · have kept : b[3] = a[3] := by simp only [b]; signature_regs
    exact bx₂.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) (kept.trans parseLen))
  · have kept : b[14] = a[14] := by simp only [b]; signature_regs
    exact r14₂.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) (kept.trans parseMsg))

end K256.Proofs.Verify.Wrapper
