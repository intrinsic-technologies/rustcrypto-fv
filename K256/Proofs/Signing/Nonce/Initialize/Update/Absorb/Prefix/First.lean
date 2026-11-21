import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.First.Blocks
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Result
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Words
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

namespace Absorb.Prefix.First

open Verify.Core.Lincomb.Recode (storeGuard)

private def copiedMemory (fr : Activation) (m : Ram) :=
  memStore (UpdateV.Append.stored (firstSaved fr m) (sp fr + 224) (fr.rdi + 32))
    (sp fr + 287) (32 : BitVec 8)

private def prefixArgs (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (seed : Bool) :=
  taggedArgs (copiedArgs (initialArgs a (sp fr) (fr.rdi + 32)) (firstSaved fr m) (fr.rdi + 32)) seed

local macro "prefix_args" : tactic =>
  `(tactic| (simp only [Atom.Holds,prefixArgs,seededArgs,taggedArgs,copiedArgs,initialArgs,
    Fin.getElem_fin,Vector.getElem_set,Nat.reduceEqDiff,↓reduceIte,Value.get_mk] <;> (first | assumption | rfl)))

private theorem tagged {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram}
    (env : Environment fr input) (live : Live (appendAt false) fr a m state)
    (ctx : UpdateV.HmacStateAt m (context fr false) state.key ByteArray.empty)
    (count : fr.rdx = if seeded input then 3 else 0) :
    Verify.Core.Reaches (appendAt false) a m (if seeded input then .l1041e3 else .l1046a2)
      (prefixArgs fr a m (seeded input)) (firstTagged fr m) := by
  obtain ⟨rsp, _, _, bp, _, _, _, r15, _⟩ := live.atoms
  have r := RamWriteFrame.refl m (area fr 8 288)
  have u := (stackWritable env live r 287 1 (by decide)).readable
  have used : memLoad m (sp fr + 287) 8 = 0 := by
    have addr : context fr false + 127 = sp fr + 287 := by
      change sp fr + 160 + 127 = _
      bv_omega
    exact addr ▸ ctx.used
  have save := initial (congrArg (Value.get 64) rsp) (congrArg (Value.get 64) bp)
    ⟨u.low,u.present⟩ used
    (storeGuard (off := 24) (stackWritable env live r 112 8 (by decide)) code_l10416d (by decide))
  have saved : RamWriteFrame m (firstSaved fr m) (area fr 8 288) :=
    stackStore (i := 112) env r (fr.rdi + 32) (by decide) (by decide) (by decide)
  have words := wordAccess env live saved 224 (by decide)
  obtain ⟨rd₁,wr₁,rd₂,eq₂,wr₂,rd₃,rd₄,eq₃,eq₄,wr₃,wr₄,wrUsed⟩ := words
  have rspBits : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have copied := copy (code := Extracted.programImage) (a := initialArgs a (sp fr) (fr.rdi+32))
    (m := firstSaved fr m) (by prefix_args) (by prefix_args) (by prefix_args) (by prefix_args)
    rd₁ (storeGuard (off := 4) wr₁ code_l104190 (by decide)) rd₂ eq₂
    (storeGuard (off := 13) wr₂ code_l104190 (by decide)) rd₃ rd₄ eq₃ eq₄
    (storeGuard (off := 25) wr₃ code_l104190 (by decide))
    (storeGuard (off := 30) wr₄ code_l104190 (by decide))
    (storeGuard (off := 38) wrUsed code_l104190 (by decide))
  have stored := storedFrame (off := 224) env saved (fr.rdi+32) (by decide) (by decide) (by decide)
  have marked : RamWriteFrame m (copiedMemory fr m) (area fr 8 288) :=
    stackStore (i := 287) env stored (32 : BitVec 8) (by decide) (by decide) (by decide)
  have tagFrame := stackStore (i := 256) env marked (0 : BitVec 8) (by decide) (by decide) (by decide)
  have countBits := (congrArg (Value.get 64) r15).trans count
  have tagged := mark (m := copiedMemory fr m) (a := copiedArgs
      (initialArgs a (sp fr) (fr.rdi+32)) (firstSaved fr m) (fr.rdi+32))
    (seeded input) (by prefix_args) (by prefix_args) (by prefix_args)
    (storeGuard (off := 0) (stackWritable env live marked 256 1 (by decide)) code_l1041c8 (by decide))
    (storeGuard (off := 11) (stackWritable env live tagFrame 287 1 (by decide)) code_l1041c8 (by decide))
  have shape : firstTagged fr m =
      memStore (memStore (copiedMemory fr m) (sp fr+256) (0 : BitVec 8)) (sp fr+287) (33 : BitVec 8) := by
    unfold firstTagged taggedMemory copiedMemory
    simp only [BitVec.add_assoc,BitVec.reduceAdd]
    rfl
  rw [← shape] at tagged
  exact .step (congrArg (Transfer.next _ []) save)
    (.step (congrArg (Transfer.next _ []) copied) (.step (congrArg (Transfer.next _ []) tagged) (.refl _)))

private theorem countAt {fr : Activation} {input : Input} (env : Environment fr input) :
    fr.rdx = if seeded input then 3 else 0 := by
  have atInput := env.slices
  cases input
  · exact atInput
  · exact atInput.2.2.1

private theorem seededRoute {fr : Activation} {secret reduced : ByteArray} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (env : Environment fr (.seeded secret reduced))
    (live : Live (appendAt false) fr a m state) :
    Verify.Core.Reaches .l1041e3 (prefixArgs fr a m true) (firstTagged fr m)
      .l10422b (seededArgs (prefixArgs fr a m true) fr.rsi) (firstResult true fr m) := by
  obtain ⟨rsp, _, _, bp, _, _, r14, r15, _⟩ := live.atoms
  have frame : RamWriteFrame m (firstTagged fr m) (area fr 8 288) := firstFrame env false
  have saved := stackStore (i := 120) env frame fr.rdi (by decide) (by decide) (by decide)
  have rspBits : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have bpBits : a[5].get 64 = fr.rdi := congrArg (Value.get 64) bp
  have baseBits : a[14].get 64 = fr.rsi := congrArg (Value.get 64) r14
  have countBits : a[15].get 64 = 3 := (congrArg (Value.get 64) r15).trans (countAt env)
  have run := beginLoop (a := prefixArgs fr a m true) (m := firstTagged fr m)
    (by prefix_args) (by prefix_args) (by prefix_args) (by prefix_args)
    (storeGuard (off := 0) (stackWritable env live frame 120 8 (by decide)) code_l1041e3 (by decide))
    (storeGuard (off := 12) (stackWritable env live saved 8 8 (by decide)) code_l1041e3 (by decide))
  exact .step (congrArg (Transfer.next _ []) run) (.refl _)

theorem _root_.K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.appendFirstPrefix {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (env : Environment fr input)
    (_roundOk : false = true → seeded input = true)
    (live : Live (appendAt false) fr a m state) (_slots : false = true → Slots fr m)
    (_buf : false = true → a[13] = ⟨64, sp fr + 392⟩)
    (ctx : UpdateV.HmacStateAt m (context fr false) state.key ByteArray.empty) :
    ∃ b n, Verify.Core.Reaches (appendAt false) a m (Absorb.afterPrefix false input) b n ∧
      Live (Absorb.afterPrefix false input) fr b n state ∧ (seeded input = true → Slots fr n) ∧
      (seeded input = true → Absorb.Cursor false fr b 0) ∧
      UpdateV.HmacStateAt n (context fr false) state.key (Absorb.taggedValue false state) := by
  have run := tagged env live ctx (countAt env)
  obtain ⟨rsp, df, _, bp, _, _, r14, r15, mx, ft, fc, old⟩ := live.atoms
  have localWrites := areaLocal (lo := 8) (hi := 288) env (by decide) (by decide)
  have tail (seed : Bool) {b : Verify.Core.Registers} : FrameTail fr b (firstResult seed fr m) :=
    frameTailAfter env (a := a) old (firstFrame env seed) localWrites
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) (seed : Bool) :
      (if seed then seededArgs (prefixArgs fr a m seed) fr.rsi else prefixArgs fr a m seed)[i].width = 64 := by
    have h5 := live.savedWidths 5 (by decide)
    have h12 := live.savedWidths 12 (by decide)
    have h14 := live.savedWidths 14 (by decide)
    have h15 := live.savedWidths 15 (by decide)
    obtain ⟨i, hi'⟩ := i
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with h | h | h | h | h | h <;> subst i <;> cases seed <;>
      simp only [Bool.false_eq_true, ite_true, ite_false] <;> prefix_args
  cases input with
  | empty =>
    refine ⟨prefixArgs fr a m false, firstResult false fr m, run, ?_, ?_, ?_, firstState env live ctx false⟩
    · exact liveAfter env live (firstFrame env false) localWrites
        ⟨by prefix_args,by prefix_args,by prefix_args,by prefix_args,by prefix_args,
          by prefix_args,by prefix_args,by prefix_args,tail false⟩
        (fun i hi => widths i hi false) (by intro h; cases h)
    · exact Bool.noConfusion
    · exact Bool.noConfusion
  | seeded secret reduced =>
    have slots := firstSlots (m := m) env
    have stateSlot : memLoad (firstResult true fr m) (fr.rsp - 592) 64 = fr.rdi := by
      rw [show fr.rsp - 592 = sp fr + 120 by unfold sp; bv_omega]
      exact slots.state
    refine ⟨seededArgs (prefixArgs fr a m true) fr.rsi, firstResult true fr m,
      run.trans (seededRoute env live), ?_, fun _ => slots, ?_, firstState env live ctx true⟩
    · exact liveAfter env live (firstFrame env true) localWrites
        ⟨by prefix_args,by prefix_args,by prefix_args,by prefix_args,by prefix_args,
          by prefix_args,stateSlot,tail true⟩
        (fun i hi => widths i hi true) (by intro h; cases h)
    · intro _
      refine ⟨?_, ?_, Bool.noConfusion, Bool.noConfusion⟩
      · simp only [prefixArgs,seededArgs,taggedArgs,copiedArgs,initialArgs,Vector.getElem_set,
          Nat.reduceEqDiff,↓reduceIte]
        change (⟨64,sp fr+224⟩ : Value) = ⟨64,context fr false+64⟩
        exact congrArg (Value.mk 64) (by change sp fr + 224 = sp fr + 160 + 64; bv_omega)
      · simp only [seededArgs, Vector.getElem_set, ↓reduceIte]
        change (⟨64,fr.rsi⟩ : Value) = ⟨64,fr.rsi + BitVec.ofNat 64 0⟩
        rw [BitVec.add_zero]

end Absorb.Prefix.First

end K256.Proofs.Signing.Nonce.Initialize.Update
