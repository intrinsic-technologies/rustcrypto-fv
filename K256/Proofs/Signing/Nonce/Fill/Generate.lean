import K256.Proofs.Signing.Nonce.Fill.Memory
import K256.Proofs.Signing.UpdateV
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Copy
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.Hash.Update.Copy
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.NIST.SHA2 Standards.RFC
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

private theorem Frame.rsp {fr : Activation} {a : Registers} {m : Ram} (frame : Frame fr a m) :
    a[4] = ⟨64, sp fr⟩ := frame.atoms.1

private theorem get64 {v : Value} {x : BitVec 64} (h : v = ⟨64, x⟩) :
    v.get 64 = x := by rw [h]; rfl

private theorem value64 (v : Value) (w : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  cases v
  cases w
  rfl

private theorem prepareBlock {a : Registers} {m : Ram} {ptr dst : BitVec 64}
    (rsp : a[4].get 64 = ptr)
    (readDst : LoadOk m (ptr + 40) 8) (readLen : LoadOk m (ptr + 48) 8)
    (dstVal : memLoad m (ptr + 40) 64 = dst) (lenVal : memLoad m (ptr + 48) 64 = 32) :
    ∃ b : Registers, Reaches .l100ab0 a m .l100ac0 b m ∧
      b[5] = ⟨64, 32⟩ ∧ b[14] = ⟨64, dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,6,7,8,9,12,13,15,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    refine .single ?_
    change Transfer.next _ [] (program.runBlock _ ⟨.l100ab0, a, m⟩) = _
    cfg_eval [rsp, readDst, readLen, dstVal, lenVal]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem valueCallBlock {a : Registers} {m : Ram} {ptr dst : BitVec 64}
    (rsp : a[4].get 64 = ptr) (bp : a[5].get 64 = 32) (r14 : a[14].get 64 = dst)
    (push : StoreOk Extracted.programImage m (ptr - 8) 8 0x100ad2 5) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l100ac0, a, m⟩ =
        .call ⟨.l104970, b, memStore m (ptr - 8) (0x100ad7 : BitVec 64)⟩ (Verify.resumeAt .l100ad7 0x100ad7) ∧
      b[4] = ⟨64, ptr - 8⟩ ∧ b[13] = ⟨64, dst + 32⟩ ∧ b[15] = ⟨64, 32⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,12,14,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, bp, r14, push]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem copyCallBlock {a : Registers} {m : Ram} {ptr dst src : BitVec 64}
    (rsp : a[4].get 64 = ptr) (r14 : a[14].get 64 = dst) (r12 : a[12].get 64 = src)
    (r15 : a[15].get 64 = 32) (rbx : a[3].get 64 = 0x12a820)
    (push : StoreOk Extracted.programImage m (ptr - 8) 8 0x100ae0 2) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l100ad7, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (ptr - 8) (0x100ae2 : BitVec 64)⟩ (Verify.resumeAt .l100ae2 0x100ae2) ∧
      b[4] = ⟨64, ptr - 8⟩ ∧ b[7] = ⟨64, dst⟩ ∧ b[6] = ⟨64, src⟩ ∧ b[2] = ⟨64, 32⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, r14, r12, r15, rbx, push]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem finishBlock {a : Registers} {m : Ram} {ptr statePtr : BitVec 64}
    (rsp : a[4].get 64 = ptr) (bp : a[5].get 64 = 32) (r15 : a[15].get 64 = 32)
    (read : LoadOk m (ptr + 64) 8) (state : memLoad m (ptr + 64) 64 = statePtr) :
    ∃ b : Registers, Reaches .l100ae2 a m .l100aef b m ∧ b[7] = ⟨64, statePtr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,7,14] → b[i].width = 64) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,6,8,9,12,13,15,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    refine .single ?_
    change Transfer.next _ [] (program.runBlock _ ⟨.l100ae2, a, m⟩) = _
    cfg_eval [rsp, bp, r15, read, state]
    rfl
  case post =>
    refine ⟨rfl, ?_, ?_⟩
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem slotAddress (fr : Activation) :
    sp fr - 8 = fr.rsp - 240 := by unfold sp; bv_omega

private theorem slotWithin {fr : Activation} (env : Environment fr) :
    InRegions (regions fr) (sp fr - 8) 8 := by
  refine ⟨fr.region, List.mem_cons_self, ?_⟩
  simp only [InRegion, Activation.region, slotAddress, env.low,
    env.subNat 2160 (by decide), env.subNat 240 (by decide), BitVec.reduceToNat]
  have := env.depth
  have := env.limit
  omega

private theorem prepare {fr : Activation} {a : Registers} {m : Ram} {state : State}
    (env : Environment fr) (head : Head fr state a m) :
    ∃ b, Reaches .l100ab0 a m .l100ac0 b m ∧ Head fr state b m ∧
      b[5] = ⟨64, 32⟩ ∧ b[14] = ⟨64, fr.rsi⟩ := by
  have dstAddr : sp fr + 40 = fr.rsp - 192 := by unfold sp; bv_omega
  have lenAddr : sp fr + 48 = fr.rsp - 184 := by unfold sp; bv_omega
  have readDst := (head.toFrame.slot env 40 8 (by decide)).readable
  have readLen := (head.toFrame.slot env 48 8 (by decide)).readable
  obtain ⟨_, _, _, _, _, dst, len, _⟩ := head.atoms
  obtain ⟨b, run, rbp, r14, kept⟩ := prepareBlock (get64 head.toFrame.rsp)
    ⟨readDst.low,readDst.present⟩ ⟨readLen.low,readLen.present⟩ (dstAddr ▸ dst)
    ((lenAddr ▸ len : memLoad m (sp fr + 48) 64 = fr.rdx).trans env.size)
  have afterWidths (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) : b[i].width = 64 := by
    have cases : i.val = 5 ∨ i.val = 14 ∨ i.val ∈ [1,2,3,4,6,7,8,9,12,13,15,22,39,50,51] := by
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    obtain ⟨i, _⟩ := i
    rcases cases with case5 | case14 | keep
    · change i = 5 at case5
      subst i
      exact congrArg Value.width rbp
    · change i = 14 at case14
      subst i
      exact congrArg Value.width r14
    · rw [kept _ keep]
      exact head.widths _ hi
  have f : Frame fr b m := head.toFrame.afterCall env (RamWriteFrame.refl m [])
    (by simp [RegionsWithin]) (by intros; rfl) ((kept 4 (by decide)).trans head.toFrame.rsp)
    (fun i hi => kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
    afterWidths
  exact ⟨b, run, ⟨f, head.stateAt, (kept 7 (by decide)).trans head.rdi,
    (kept 12 (by decide)).trans head.r12, (kept 3 (by decide)).trans head.rbx⟩, rbp, r14⟩

private def valueChild (fr : Activation) (a : Registers) (m : Ram) : Activation :=
  {fr with
    original := m, rsp := fr.rsp - 240, low := fr.rsp - 1440, ret := 0x100ad7,
    rdi := fr.rdi + 8, rbx := a[3].get 64, rbp := a[5].get 64, r12 := a[12].get 64,
    r13 := a[13].get 64, r14 := a[14].get 64, r15 := a[15].get 64, rsi := a[6].get 64,
    rdx := a[2].get 64, rcx := a[1].get 64, r8 := a[8].get 64, r9 := a[9].get 64 }

private structure ValueReady (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop
    extends Frame fr a m where
  stateAt : StateAt m (fr.rdi + 8) (Drbg.updateValue state)
  r12 : a[12] = ⟨64,fr.rdi+40⟩
  rbx : a[3] = ⟨64,0x12a820⟩
  rbp : a[5] = ⟨64,32⟩
  r14 : a[14] = ⟨64,fr.rsi⟩
  r15 : a[15] = ⟨64,32⟩

set_option maxHeartbeats 600000 in
private theorem updateValue {fr : Activation} {state : State} {a : Registers} {m : Ram}
    (env : Environment fr) (ready : Head fr state a m)
    (bp : a[5] = ⟨64,32⟩) (dst : a[14] = ⟨64,fr.rsi⟩) :
    ∃ b n, Reaches .l100ac0 a m .l100ad7 b n ∧ ValueReady fr state b n := by
  let pushed := memStore m (sp fr - 8) (0x100ad7 : BitVec 64)
  have pushW := ready.toFrame.pushSlot env
  have guard : StoreOk Extracted.programImage m (sp fr - 8) 8 0x100ad2 5 :=
    ParseSignature.storeOk_of_codeRange (off := 18) pushW
      (fun x hx => Common.fnCode_subset_programImage x (code_l100ac0 x hx)) (by decide)
  obtain ⟨c, call, rsp, r13, r15, kept⟩ := valueCallBlock
    (get64 ready.toFrame.rsp) (get64 bp) (get64 dst) guard
  let child := valueChild fr c pushed
  have depth := env.depth
  have lim := env.limit
  have lowNat : child.low.toNat = fr.rsp.toNat - 1440 := env.subNat 1440 (by decide)
  have rspNat : child.rsp.toNat = fr.rsp.toNat - 240 := env.subNat 240 (by decide)
  have slotNat : (sp fr - 8).toNat = fr.rsp.toNat - 240 := env.pushNat
  have diNat : child.rdi.toNat = fr.rsp.toNat + 704 := by
    change (fr.rdi + 8).toNat = _
    rw [env.gen, show fr.rsp + 696 + 8 = fr.rsp + 704 by bv_omega, env.addNat 704 (by decide)]
    rfl
  have rd : Readable pushed child.rsp 8 := by
    change Readable pushed (fr.rsp - 240) 8
    rw [← slotAddress]
    exact pushW.readable.memStore _ _
  have ret : memLoad pushed child.rsp 64 = child.ret := by
    change memLoad pushed (fr.rsp - 240) 64 = 0x100ad7
    rw [← slotAddress]; exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have childStack : Writable Extracted.programImage pushed (child.rsp - 1200) 1200 := by
    change Writable _ pushed (fr.rsp - 240 - 1200) 1200
    rw [show fr.rsp - 240 - 1200 = fr.rsp - 1440 by bv_omega]
    apply (ready.toFrame.stack.memStore (sp fr - 8) (0x100ad7 : BitVec 64)).sub
    all_goals rw [env.subNat 1440 (by decide), env.subNat 2160 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
  have pushFrame : RamWriteFrame fr.original pushed (regions fr) :=
    ready.writes.memStore _ (slotWithin env)
  have image := ready.toFrame.imageAfter env pushFrame
  have tables := Fn104970.callSlots_loaded (sections := Extracted.programSections)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) image
  obtain ⟨rCopy, vCopy⟩ := tables (0x203dd0,0x12a820) (by decide)
  obtain ⟨rSet, vSet⟩ := tables (0x203e10,0x12a700) (by decide)
  have childWidth (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) : c[i].width = 64 := by
    have cases : i.val = 4 ∨ i.val = 13 ∨ i.val = 15 ∨
        i.val ∈ [1,2,3,5,6,7,8,9,12,14,22,39,50,51] := by
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    obtain ⟨i, _⟩ := i
    rcases cases with eq | eq | eq | keep
    · change i = 4 at eq
      subst i
      exact congrArg Value.width rsp
    · change i = 13 at eq
      subst i
      exact congrArg Value.width r13
    · change i = 15 at eq
      subst i
      exact congrArg Value.width r15
    · rw [kept _ keep]
      exact ready.widths _ hi
  have preserve (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : c[i] = a[i] :=
    kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  obtain ⟨_,df,mx,ft,fc,_,_,_,_,_,_,_,_,_,_,_,_,_,_,align,_,_,_,_,_,_,_,_,gap,_⟩ := ready.atoms
  have entry : Atom.All Extracted.programImage c pushed (Fn104970.frameAt .l104970 child) := by
    change fr.rsp.toNat % 16 = 8 at align
    change 0x204698 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at gap
    simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds, Atom.gpr]
    refine ⟨(show c[4] = ⟨64,fr.rsp - 240⟩ from (slotAddress fr) ▸ rsp), (preserve 22 (by decide)).trans df,
      value64 _ (childWidth 1 (by decide)), value64 _ (childWidth 2 (by decide)),
      value64 _ (childWidth 3 (by decide)), value64 _ (childWidth 5 (by decide)),
      value64 _ (childWidth 6 (by decide)), (kept 7 (by decide)).trans ready.rdi,
      value64 _ (childWidth 8 (by decide)), value64 _ (childWidth 9 (by decide)),
      value64 _ (childWidth 12 (by decide)), value64 _ (childWidth 13 (by decide)),
      value64 _ (childWidth 14 (by decide)), value64 _ (childWidth 15 (by decide)),
      (preserve 39 (by decide)).trans mx, (preserve 50 (by decide)).trans ft,
      (preserve 51 (by decide)).trans fc, rd, ret, (by change (0x100ad7 : BitVec 64).toNat < 2^32; decide), childStack, ?_, ?_,
      rCopy, vCopy, rSet, vSet, ?_, trivial⟩
    · change child.low.toNat + 1200 ≤ child.rsp.toNat
      omega
    · change child.rsp.toNat % 16 = 8
      omega
    · change 0x2042c8 ≤ child.rsp.toNat ∨ child.rsp.toNat ≤ 0x203dd0
      omega
  have input : StateAt pushed (fr.rdi+8) state := by
    apply stateAfter ((RamWriteFrame.refl m [⟨(sp fr - 8).toNat,8⟩]).memStore (0x100ad7 : BitVec 64) ?_)
      ?_ ready.stateAt
    · exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by rw [slotNat]; omega⟩
    · change Outside [⟨(sp fr - 8).toNat,8⟩] child.rdi 64
      refine ⟨by omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inr (by dsimp only; omega)
  have dataW : Writable Extracted.programImage pushed child.rdi 64 := by
    apply (env.window.of_frame pushFrame).sub <;> omega
  obtain ⟨out, run, tag, post, calleeWrites, args, value⟩ :=
    UpdateV.execution (fr := child) entry image (by change fr.rsp - 1440 = fr.rsp - 240 - 1200; bv_omega)
      (by omega) (by omega) (by omega) (Or.inr (by omega)) dataW input.key input.value
  let rs : List MemoryRegion := [⟨child.low.toNat,1208⟩, ⟨child.rdi.toNat + 32,32⟩]
  have writes : RamWriteFrame m out.store rs := by
    apply ((RamWriteFrame.refl m rs).memStore (0x100ad7 : BitVec 64) ?_).trans calleeWrites
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_cons_self, ?_, ?_⟩
        · exact Nat.le_refl _
        · change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ child.low.toNat + 1208
          omega
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change child.low.toNat ≤ (sp fr - 8).toNat ∧
        (sp fr - 8).toNat + 8 ≤ child.low.toNat + 1208 ∧ (sp fr - 8).toNat + 8 ≤ 2^64
      omega
  have within : RegionsWithin rs (regions fr) := by
    intro r hr
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩ <;>
        simp only [Activation.region, env.low, env.subNat 2160 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        by change (fr.rdi+8).toNat ≤ child.rdi.toNat + 32; change child.rdi.toNat ≤ _; omega,
        by change child.rdi.toNat + 32 + 32 ≤ child.rdi.toNat + 64; omega⟩
  have memory (k : BitVec 64) (w : Nat) (hk : k.toNat ≤ 232) (hw : w ≤ 64) :
      memLoad out.store (fr.rsp - k) w = memLoad m (fr.rsp - k) w := by
    apply writes.memLoad_eq
    have pos := env.subNat k (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (by dsimp only; omega)
    · exact Or.inl (by dsimp only; omega)
  have keyOutside : Outside rs child.rdi 32 := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (by dsimp only; omega)
    · exact Or.inl (Nat.le_refl _)
  have bytes : StateAt out.store (fr.rdi+8) (Drbg.updateValue state) := by
    have key := UpdateV.Finalize.bytesAfter (p := fr.rdi+8) (n := 32) (bs := state.key)
      writes keyOutside ready.stateAt.key
    unfold Drbg.updateValue
    exact ⟨key, value⟩
  simp only [Fn104970.doneAt, Atom.All, Atom.Holds, Atom.gpr] at post
  obtain ⟨rs', df', bx', bp', r12', r13', r14', r15', mx', ft', fc', _⟩ := post
  have saved (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      out.values[i] = c[i] := by
    have w := (value64 _ (childWidth i (Activation.calleeSavedNumbers_sub _ hi))).symm
    obtain ⟨i, _⟩ := i
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h <;> change i = _ at h <;> subst i
    · exact bx'.trans w
    · exact bp'.trans w
    · exact r12'.trans w
    · exact r13'.trans w
    · exact r14'.trans w
    · exact r15'.trans w
  have rsp' : out.values[4] = ⟨64,sp fr⟩ :=
    rs'.trans (congrArg (Value.mk 64) (show child.rsp + 8 = sp fr by change fr.rsp - 240 + 8 = _; unfold sp; bv_omega))
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) : out.values[i].width = 64 := by
    have cases : i.val = 4 ∨ i.val ∈ Activation.calleeSavedNumbers ∨ i.val ∈ Activation.argumentNumbers := by
      simp only [Activation.entryNumbers, Activation.calleeSavedNumbers, Activation.argumentNumbers,
        List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rcases cases with h | h | h
    · obtain ⟨i, _⟩ := i
      change i = 4 at h
      subst i
      exact congrArg Value.width rsp'
    · rw [saved i h]; exact childWidth i hi
    · exact args i h
  have regs (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : out.values[i] = a[i] := by
    obtain ⟨i, _⟩ := i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h <;> change i = _ at h <;> subst i
    · exact df'.trans (show a[22] = ⟨1,0⟩ from df).symm
    · exact mx'.trans (show a[39] = ⟨32,fr.mxcsr⟩ from mx).symm
    · exact ft'.trans (show a[50] = ⟨16,fr.ftw⟩ from ft).symm
    · exact fc'.trans (show a[51] = ⟨16,fr.fcw⟩ from fc).symm
  exact ⟨out.values, out.store, Verify.reachesOfCall call run tag,
    ready.toFrame.afterCall env writes within (fun k w h => by
      rcases h with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
      · apply memory _ _ _ (by decide)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        omega
      · exact memory _ _ (by decide) (by decide)) rsp' regs widths, bytes,
    (saved 12 (by decide)).trans ((kept 12 (by decide)).trans ready.r12),
    (saved 3 (by decide)).trans ((kept 3 (by decide)).trans ready.rbx),
    (saved 5 (by decide)).trans ((kept 5 (by decide)).trans bp),
    (saved 14 (by decide)).trans ((kept 14 (by decide)).trans dst),
    (saved 15 (by decide)).trans r15⟩

private theorem copyValue {fr : Activation} {state : State} {a : Registers} {m : Ram}
    (env : Environment fr) (ready : ValueReady fr state a m) :
    ∃ b n, Reaches .l100ad7 a m .l100aef b n ∧ Generated fr state b n := by
  let slot := sp fr - 8
  let pushed := memStore m slot (0x100ae2 : BitVec 64)
  have pushW := ready.toFrame.pushSlot env
  have guard : StoreOk Extracted.programImage m slot 8 0x100ae0 2 :=
    ParseSignature.storeOk_of_codeRange (off := 9) pushW
      (fun x hx => Common.fnCode_subset_programImage x (code_l100ad7 x hx)) (by decide)
  obtain ⟨c, call, rc4, rc7, rc6, rc2, kept⟩ := copyCallBlock (get64 ready.toFrame.rsp)
    (get64 ready.r14) (get64 ready.r12) (get64 ready.r15) (get64 ready.rbx) guard
  have depth := env.depth
  have lim := env.limit
  have slotNat : slot.toNat = fr.rsp.toNat - 240 := env.pushNat
  have dstNat : fr.rsi.toNat = fr.rsp.toNat + 392 := by rw [env.dst, env.addNat 392 (by decide)]; rfl
  have srcNat : (fr.rdi + 40).toNat = fr.rsp.toNat + 736 := by
    rw [env.gen, show fr.rsp + 696 + 40 = fr.rsp + 736 by bv_omega, env.addNat 736 (by decide)]
    rfl
  have stateNat : (fr.rdi + 8).toNat = fr.rsp.toNat + 704 := by
    rw [env.gen, show fr.rsp + 696 + 8 = fr.rsp + 704 by bv_omega, env.addNat 704 (by decide)]
    rfl
  have ret : memLoad pushed slot 64 = 0x100ae2 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have w : Writable Extracted.programImage pushed fr.rsp 768 :=
    (env.window.of_frame ready.writes).memStore _ _
  have read : Readable pushed (fr.rdi+40) 32 := w.readable.sub (by omega) (by omega)
  have write : Writable Extracted.programImage pushed fr.rsi 32 := w.sub (by omega) (by omega)
  have direction : c[22] = ⟨1,0⟩ := (kept 22 (by decide)).trans ready.atoms.2.1
  have retApart : RangeApart fr.rsi 32 slot 8 :=
    RangeApart.of_toNat (by omega) (by omega) (Or.inr (by omega))
  obtain ⟨out, run, copy, tag, _, outSp, preserved⟩ := Verify.Hash.Update.memcpy
    (rsp := slot) (count := 32)
    (get64 rc7) (get64 rc6) (get64 rc2) (get64 rc4) (by rw [direction]; rfl) read write
    (Or.inr (by change fr.rsi.toNat + 32 ≤ _; omega)) (by exact retApart)
    (pushW.readable.memStore _ _) (by rw [ret]; decide)
  have r9 : c[9].width = 64 :=
    (congrArg Value.width (kept 9 (by decide))).trans (ready.widths 9 (by decide))
  have args := Initialize.Encode.copyArgumentWidths run r9
  let rs : List MemoryRegion := [⟨slot.toNat,8⟩, ⟨fr.rsi.toNat,32⟩]
  have pushedFrame : RamWriteFrame m pushed rs :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
  have writes : RamWriteFrame m out.store rs := by
    rw [copy, show (32 : BitVec 64).toNat = 32 by decide]
    apply Sec1.Wrapper.Copy.memCopy_frame pushedFrame
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _, by omega⟩
  have within : RegionsWithin rs (regions fr) := by
    intro r hr
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩ <;>
        simp only [Activation.region, env.low, env.subNat 2160 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have memory (k : BitVec 64) (width : Nat) (hk : k.toNat ≤ 232) (hw : width ≤ 64) :
      memLoad out.store (fr.rsp - k) width = memLoad m (fr.rsp - k) width := by
    apply writes.memLoad_eq
    have pos := env.subNat k (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (by dsimp only; omega)
    · exact Or.inl (by dsimp only; omega)
  have outside : Outside rs (fr.rdi + 8) 64 := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inr (by dsimp only; omega)
  have unchanged := stateAfter writes outside ready.stateAt
  have pushedState := stateAfter pushedFrame outside ready.stateAt
  have srcBytes : (⟨(fr.rdi+40).toNat,32⟩ : MemoryRegion).HasBytes pushed
      (Drbg.updateValue state).value := by
    rw [srcNat, show fr.rsp.toNat + 736 = fr.rsp.toNat + 704 + 32 by omega, ← stateNat]
    exact pushedState.value
  have copiedBytes : (⟨fr.rsi.toNat,32⟩ : MemoryRegion).HasBytes out.store (Drbg.updateValue state).value := by
    rw [copy]
    exact Sec1.Wrapper.Copy.memCopy_hasBytes (by decide) srcBytes
  have resume := Verify.reachesOfCall call run (tag.trans (congrArg (fun r => some (Value.mk 64 r)) ret))
  have kept' (i : Fin Reg.count) (hi : i.val ∈ [3,5,9,12,13,14,15,22,39,50,51]) :
      out.values[i] = a[i] := by
    exact (preserved i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (kept i hi)
  have rsp : out.values[4] = ⟨64,sp fr⟩ := by
    rw [outSp, BitVec.sub_add_cancel]
  have slotState : memLoad out.store (sp fr + 64) 64 = fr.rdi + 8 := by
    have eq : sp fr + 64 = fr.rsp - 168 := by unfold sp; bv_omega
    exact (eq ▸ memory 168 64 (by decide) (by decide)).trans ready.statePtr
  have readState := (ready.toFrame.slot env 64 8 (by decide)).readable.of_frame writes
  obtain ⟨b, finish, rdi, newWidth, finalKept⟩ := finishBlock (get64 rsp)
    (get64 ((kept' 5 (by decide)).trans ready.rbp)) (get64 ((kept' 15 (by decide)).trans ready.r15))
    ⟨readState.low,readState.present⟩ slotState
  have finalWidth (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) : b[i].width = 64 := by
    have cases : i.val ∈ [5,7,14] ∨ i.val = 4 ∨
        i.val ∈ [3,12,13,15] ∨ i.val ∈ [1,2,6,8,9] := by
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have byKept (h : i.val ∈ [1,2,3,4,6,8,9,12,13,15,22,39,50,51])
        (w : out.values[i].width = 64) : b[i].width = 64 := by
      rw [finalKept i h]
      exact w
    rcases cases with n | rs | saved | arg
    · exact newWidth i n
    · obtain ⟨i, _⟩ := i
      change i = 4 at rs
      subst i
      exact byKept (of_decide_eq_true rfl) (congrArg Value.width rsp)
    · apply byKept (by simp only [List.mem_cons, List.not_mem_nil, or_false] at saved ⊢; omega)
      rw [kept' i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at saved ⊢; omega)]
      exact ready.widths i hi
    · exact byKept (by simp only [List.mem_cons, List.not_mem_nil, or_false] at arg ⊢; omega)
        (args i (by simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at arg ⊢; omega))
  have regs (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : b[i] = a[i] :=
    (finalKept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (kept' i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  exact ⟨b, out.store, resume.trans finish,
    ready.toFrame.afterCall env writes within (fun k w h => by
      rcases h with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
      · apply memory _ _ _ (by decide)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        omega
      · exact memory _ _ (by decide) (by decide)) ((finalKept 4 (by decide)).trans rsp) regs finalWidth,
    unchanged, copiedBytes, rdi⟩

theorem generate {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (head : Head fr state a m) :
    ∃ c t b n, Reaches .l100ab0 a m .l100ac0 c t ∧ Reaches .l100ac0 c t .l100aef b n ∧
      Generated fr state b n := by
  obtain ⟨c, front, prepared, bp, dst⟩ := prepare env head
  obtain ⟨d, t, value, ready⟩ := updateValue env prepared bp dst
  obtain ⟨b, n, copy, generated⟩ := copyValue env ready
  exact ⟨c, m, b, n, front, value.trans copy, generated⟩

end K256.Proofs.Signing.Nonce.Fill
