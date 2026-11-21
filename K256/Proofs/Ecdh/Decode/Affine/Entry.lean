import K256.Proofs.Ecdh.Decode.Affine.Contract

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Sec1.Affine

theorem Entry.start {fr : Activation} {args m bytes} (e : Entry fr args m bytes) :
    let tag := (bytes.data[0]?.getD 0).toBitVec
    let label := if 2 ≤ tag.toNat ∧ tag.toNat < 6 then Label.l1214a0 else .l1214d0
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l121480,args,m⟩ =
        .jump ⟨label,next,saveRegisters args m⟩ ∧
      next[0] = ⟨64,tag.setWidth 64⟩ ∧ next[1] = ⟨64,tag.setWidth 64⟩ ∧ next[2] = ⟨64,fr.rsi⟩ ∧
      Atom.All Extracted.programImage next (saveRegisters args m) (Fn121480.frameAt .l121599 fr) ∧
      RamWriteFrame m (saveRegisters args m) [⟨(fr.rsp-40).toNat,40⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,15] → next[i] = args[i]) := by
  dsimp only
  let tag := (bytes.data[0]?.getD 0).toBitVec
  have room := e.low
  have base : (fr.rsp-40).toNat = fr.rsp.toNat-40 :=
    BitVec.toNat_sub_of_le (by change 40 ≤ fr.rsp.toNat; omega)
  have outside {p : BitVec 64} {n : Nat} (lo : p.toNat+n ≤ 2^32) (above : fr.rsp.toNat ≤ p.toNat) :
      Outside [⟨(fr.rsp-40).toNat,40⟩] p n := by
    refine ⟨by omega,fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp-40).toNat + 40 ≤ p.toNat
    omega
  have savedWrite : Writable Extracted.programImage m (fr.rsp-40) 40 :=
    e.window.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have sp : args[4].get 64 = fr.rsp := congrArg (Value.get 64) e.rsp
  have tagEq : memLoad m fr.rsi 8 = tag := by
    apply memLoad_eq_of_memByte (by decide)
    intro j hj
    obtain rfl : j = 0 := by omega
    exact (e.bytesAt 0 (by decide)).trans (by simp [tag, storedByte])
  have read : Readable m fr.rsi 1 := e.input.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide) _)
  obtain ⟨next, step, ax, cx, dx, bx, rsp, writes, keeps⟩ :=
    affineEntry Common.fnCode_subset_programImage args m fr.rsp fr.rsi fr.rdi sp
      (congrArg (Value.get 64) e.src) (congrArg (Value.get 64) e.dst) savedWrite (by omega)
      read (outside read.low (by have := e.srcAbove; omega))
  have init := e.saved
  have saved := savedSlots args m
  dsimp only at saved
  rw [sp] at saved
  obtain ⟨b, r12, r14, r15, bp⟩ := saved
  have kept (i : Fin Reg.count) (hi : i.val ∈ [13,39,50,51]) : next[i] = fr.entryValue i.val :=
    (keeps i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      (init i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  have retAfter := (writes.memLoad_eq (k := 64) (outside e.slot.low (Nat.le_refl _))).trans e.ret
  rw [tagEq] at ax cx step
  refine ⟨next, ?_, ax, cx, dx, ?_, writes, fun i hi => keeps i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)⟩
  · have choose {α : Type} (P : Prop) [Decidable P] (f : Label → α) :
        (if decide P then f .l1214a0 else f .l1214d0) = f (if P then .l1214a0 else .l1214d0) := by
      by_cases h : P <;> simp [h]
    exact step.trans (choose (2 ≤ tag.toNat ∧ tag.toNat < 6) (fun l => Transfer.jump ⟨l,next,saveRegisters args m⟩))
  · simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds]
    refine ⟨rsp,(keeps 22 (by decide)).trans e.df,bx,kept 13 (by decide),kept 39 (by decide),
      kept 50 (by decide),kept 51 (by decide), b.trans (congrArg (Value.get 64) (init 3 (by decide))),
      r12.trans (congrArg (Value.get 64) (init 12 (by decide))),
      r14.trans (congrArg (Value.get 64) (init 14 (by decide))),
      r15.trans (congrArg (Value.get 64) (init 15 (by decide))),
      bp.trans (congrArg (Value.get 64) (init 5 (by decide))),
      e.slot.of_frame writes, retAfter, e.retLow, e.window.of_frame writes, e.low, e.align, trivial⟩

theorem Entry.returnedRegisters {fr : Activation} {args m bytes} {out : Output Value Ram Reg.count}
    (e : Entry fr args m bytes) (done_ : Atom.All Extracted.programImage out.values out.store
      (Fn121480.doneAt fr)) : out.values[4] = ⟨64,fr.rsp+8⟩ ∧
    ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i] := by
  simp only [Fn121480.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨sp,df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := done_
  have kept := e.saved
  refine ⟨sp, ?_⟩
  rintro ⟨i,hi⟩ h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact df.trans e.df.symm
    | exact bx.trans (kept 3 (by decide)).symm
    | exact bp.trans (kept 5 (by decide)).symm
    | exact r12.trans (kept 12 (by decide)).symm
    | exact r13.trans (kept 13 (by decide)).symm
    | exact r14.trans (kept 14 (by decide)).symm
    | exact r15.trans (kept 15 (by decide)).symm
    | exact mx.trans (kept 39 (by decide)).symm
    | exact ft.trans (kept 50 (by decide)).symm
    | exact fc.trans (kept 51 (by decide)).symm

end K256.Proofs.Ecdh.Decode.Affine
