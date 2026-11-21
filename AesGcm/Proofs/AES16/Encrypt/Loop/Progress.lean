import AesGcm.Proofs.AES16.Encrypt.Loop.Calls

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

theorem native_of_span {use256 : Bool} {fr : Activation} {before after : Ram}
    {a : BitVec 64} {n : Nat} (h : RamWriteFrame before after [span a n])
    (hlo : (callPointer use256 fr).toNat ≤ a.toNat)
    (hhi : a.toNat + n ≤ (callPointer use256 fr).toNat + (if use256 then 56 else 48)) :
    RamWriteFrame before after (nativeRegions use256 fr) := by
  apply (RamWriteFrame.refl before (nativeRegions use256 fr)).trans h
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨span (callPointer use256 fr) (if use256 then 56 else 48),
    List.mem_cons_self, hlo, hhi⟩

theorem key_apart {v : Variant} {fr : Activation} {mem : Ram}
    (hread : Readable mem fr.rsi (16 * (v.Nr + 1)))
    (hsep : (callStack fr).Disjoint (span fr.rsi (16 * (v.Nr + 1))))
    (hlow : fr.low.toNat ≤ fr.rsp.toNat)
    (r : Fin (v.Nr + 1)) (a : BitVec 64) (n : Nat)
    (ha : fr.low.toNat ≤ a.toNat) (hb : a.toNat + n ≤ fr.rsp.toNat) :
    a.toNat + n ≤ (fr.rsi + BitVec.ofNat 64 (16 * r.val)).toNat ∨
      (fr.rsi + BitVec.ofNat 64 (16 * r.val)).toNat + 16 ≤ a.toNat := by
  have hs := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat (16 * (v.Nr + 1)) (by omega) (by omega) hsep
  have hr := r.isLt
  have hrlow := hread.low
  have haddr : (fr.rsi + BitVec.ofNat 64 (16 * r.val)).toNat =
      fr.rsi.toNat + 16 * r.val := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [haddr]
  omega

theorem stack_addresses (use256 : Bool) (fr : Activation) :
    (fr.rsp - (if use256 then 120 else 104)) - 8 = callPointer use256 fr ∧
    (fr.rsp - (if use256 then 120 else 104)) + (if use256 then 8 else 0) = buffer use256 fr ∧
    (fr.rsp - (if use256 then 120 else 104)) + (if use256 then 48 else 40) =
      fr.rsp - (if use256 then 72 else 64) := by
  cases use256 <;> refine ⟨?_,?_,?_⟩
  all_goals simp only [callPointer,buffer,Bool.false_eq_true,↓reduceIte]
  all_goals bv_omega

set_option maxHeartbeats 600000 in
theorem call_advance (use256 : Bool) (kind : Fin 3) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (fr : Activation)
    (before callee : LIR.lifted.Location) (target : LIR.Label) (ret : BitVec 64)
    (hwork : WorkingState code use256 key fr before)
    (hbefore : frameAt use256 before.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr)
    (htarget : frameAt use256 target fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16 * ((variant use256).Nr + 1))))
    (hcall : LIR.program.runBlock (dialect code) before = .call callee
      {target := target,kept := #v[],arity := rfl,guard := some ⟨64,ret⟩})
    (hlabel : callee.label = helperLabel kind)
    (hTypes : GPRsTyped callee.arguments)
    (hsp : callee.arguments[4]'(by change 4 < 53; decide) = ⟨64,callPointer use256 fr⟩)
    (hbuffer : callee.arguments[7]'(by change 7 < 53; decide) = ⟨64,buffer use256 fr⟩)
    (hlen : kind = 0 → callee.arguments[6]'(by change 6 < 53; decide) = ⟨64,8⟩)
    (hpres : ∀ r : Fin Reg.count, r.val ∈ [3,22,39,50,51] →
      callee.arguments[r.val]'r.isLt = before.arguments[r.val]'r.isLt)
    (hRet : memLoad callee.store (callPointer use256 fr) 64 = ret)
    (hRetLow : ret.toNat < 2^32)
    (hNative : RamWriteFrame before.store callee.store (nativeRegions use256 fr))
    (planes : Planes16)
    (hWords : WordsAt callee.store (buffer use256 fr) 16 (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨before,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧ next.label = target ∧
      WordsAt next.store (buffer use256 fr) 16 (Vector.ofFn (helperTransform kind planes)) ∧
      next.arguments[4]'(by change 4 < 53; decide) = before.arguments[4]'(by change 4 < 53; decide) ∧
      (∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15,39,50,51] →
        next.arguments[r.val]'r.isLt = callee.arguments[r.val]'r.isLt) := by
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨hNativeFrame,hNativeWhole⟩ := native_frame use256 code fr
    before.arguments before.arguments before.store callee.store hcanonical hNative (by intro _ _; rfl)
  obtain ⟨out,he,htag,htyped,hChild,hframeout,hwords,hspout,hSame⟩ :=
    execute_helper use256 kind code hcode fr before.arguments callee.arguments callee.store
      planes ret hNativeFrame hTypes hsp hbuffer hlen hpres hRet hRetLow hWords
  have hexec : LIR.program.Exec (dialect code) ⟨callee,[]⟩ out := by
    rcases callee with ⟨lab,args,mem⟩
    dsimp only at hlabel he ⊢
    subst lab
    exact he
  let continuation : LIR.lifted.StackFrame :=
    {target := target,kept := #v[],arity := rfl,guard := some ⟨64,ret⟩}
  have hResume := CFGCall.exec_reaches_resume hexec continuation [] (by rw [htag]; simp only [continuation, StackFrame.Accepts, dialect]; decide)
  change (LIR.program.sem (dialect code)).Reaches
    ⟨callee,[continuation]⟩ ⟨⟨target,out.values,out.store⟩,[]⟩ at hResume
  have hWhole := hNativeWhole.trans hChild
    (by intro r hr; exact ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  obtain ⟨_,_,_,hroom,_,_⟩ := frame_facts use256 code fr before.arguments before.store hcanonical
  have houtside := key_outside (by omega : fr.low.toNat ≤ fr.rsp.toNat) hwork.readable hsep
  refine ⟨⟨target,out.values,out.store⟩,?_,?_,rfl,hwords,hspout,hSame⟩
  · apply (Semantics.Reaches.single ?_).trans hResume
    change LIR.program.step (dialect code) ⟨before,[]⟩ = .next ⟨callee,[continuation]⟩
    rw [Program.step,hcall]
    rfl
  · apply hwork.advance (by rw [htarget]; exact hframeout) htyped hWhole houtside

theorem jump_advance (use256 : Bool) (code : CodeMap)
    (key : Vector UInt8 (variant use256).keyBytes) (fr : Activation)
    (before after : LIR.lifted.Location)
    (hwork : WorkingState code use256 key fr before)
    (hbefore : frameAt use256 before.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr)
    (hafter : frameAt use256 after.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hrun : LIR.program.runBlock (dialect code) before = .jump after)
    (htyped : GPRsTyped after.arguments)
    (hNative : RamWriteFrame before.store after.store (nativeRegions use256 fr))
    (hregs : ∀ r : Fin Reg.count, r.val ∈ [3,4,22,39,50,51] →
      after.arguments[r.val]'r.isLt = before.arguments[r.val]'r.isLt) :
    (LIR.program.sem (dialect code)).Reaches ⟨before,[]⟩ ⟨after,[]⟩ ∧
      WorkingState code use256 key fr after := by
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨hf,hWhole⟩ := native_frame use256 code fr before.arguments after.arguments
    before.store after.store hcanonical hNative hregs
  obtain ⟨_,_,_,hroom,_,_⟩ := frame_facts use256 code fr before.arguments before.store hcanonical
  refine ⟨Semantics.Reaches.single ?_,?_⟩
  · change LIR.program.step (dialect code) ⟨before,[]⟩ = .next ⟨after,[]⟩
    rw [Program.step,hrun]
    rfl
  · apply hwork.advance (by rw [hafter]; exact hf) htyped hWhole
      (key_outside (by omega : fr.low.toNat ≤ fr.rsp.toNat) hwork.readable hsep)

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
