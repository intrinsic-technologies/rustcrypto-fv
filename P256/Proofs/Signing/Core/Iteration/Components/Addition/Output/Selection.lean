import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.Low
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.Second
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.Third
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.High
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.Output
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice.Run

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field (BinaryFieldPre)
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program (CalleePre programText_slice programLoaded_codeIn)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (selectWord selectWord_zero selectWord_one)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace Selection

def frame (s : RamState) : List Component :=
  [.reg 1,.reg 2,.reg 3,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11,
    .flags,.rip,.mem (stackPtr s) 1]

theorem writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t) :
    WritesWithin (frame t) #v[registerRegion s .rdi 32, workRegion s] := by
  intro c hc a ha
  simp only [frame,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  refine ⟨workRegion s,by simp,?_⟩
  rw [state.rsp] at ha
  exact work_contains pre (by decide) (by decide) ha

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {bytes : List UInt8} {E : RamState → Effect}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (block : AdvanceTriple boundary (Pre (Extracted.textAddress + BitVec.ofNat 64 offset))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (size : offset+bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (within : (E t).components ⊆ frame t) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ (E t).Holds t u := by
  have writable : MemWritable t (stackPtr t) 1 := by
    simpa only [BitVec.add_zero] using writable_byte pre state (offset := 0) (by decide)
  have apart : ∀ i n : Nat, i+n ≤ 118431 →
      RangeApart (stackPtr t) 1 (Extracted.textAddress+BitVec.ofNat 64 i) n := by
    intro i n bound
    simpa only [BitVec.add_zero] using stack_code pre state (offset := 0) (by decide) bound
  obtain ⟨fuel,u,adv,ready,_,effect⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes size code)
    ⟨rip,writable,apart⟩
  exact ⟨fuel,u,adv,state.after_effect pre ready (effect.agrees.mono within)
    (writes pre state) (by simp [frame]),effect⟩

end Selection

open Selection in
theorem selection_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {keep : Bool}
    (pre : BinaryFieldPre s boundary 0x113310 64) (state : FrameState s t)
    (rip : t.RIP = 0x113a75) (output : t.regValue .rax = s.regValue .rdi)
    (choice : (t.regValue .rcx).setWidth 8 = if keep then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x113ad3 ∧
      Nat256At u (s.regValue .rdi)
        (if keep then (sumLimbs t).toNat else (differenceLimbs t).toNat) := by
  obtain ⟨n1,t1,adv1,state1,e1⟩ := run (offset := 0x13a75)
    pre.toCalleePre state rip (low_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel)
    (by simp [lowEffect,Effect.components,frame])
  obtain ⟨n2,t2,adv2,state2,e2⟩ := run (offset := 0x13a8b)
    pre.toCalleePre state1 e1.rip (second_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel)
    (by simp [secondEffect,Effect.components,frame])
  obtain ⟨n3,t3,adv3,state3,e3⟩ := run (offset := 0x13a9e)
    pre.toCalleePre state2 e2.rip (third_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel)
    (by simp [thirdEffect,Effect.components,frame])
  obtain ⟨n4,t4,adv4,state4,e4⟩ := run (offset := 0x13ab1)
    pre.toCalleePre state3 e3.rip (high_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel)
    (by simp [highEffect,Effect.components,frame])
  have r10 : t1.regValue .r10 = t.regValue .r10 :=
    (e1.agrees.read (n := 64) (r := 10) (by simp [lowEffect,Effect.components]))
  have rsi : t1.regValue .rsi = t.regValue .rsi :=
    (e1.agrees.read (n := 64) (r := 6) (by simp [lowEffect,Effect.components]))
  have rcx : t3.regValue .rcx = t.regValue .rcx :=
    (e3.agrees.read (n := 64) (r := 1) (by simp [thirdEffect,Effect.components])).trans ((e2.agrees.read (n := 64) (r := 1) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 1) (by simp [lowEffect,Effect.components]))))
  have r9 : t2.regValue .r9 = t.regValue .r9 :=
    (e2.agrees.read (n := 64) (r := 9) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 9) (by simp [lowEffect,Effect.components])))
  have r14 : t2.regValue .r14 = t.regValue .r14 :=
    (e2.agrees.read (n := 64) (r := 14) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 14) (by simp [lowEffect,Effect.components])))
  have r8 : t3.regValue .r8 = t.regValue .r8 :=
    (e3.agrees.read (n := 64) (r := 8) (by simp [thirdEffect,Effect.components])).trans ((e2.agrees.read (n := 64) (r := 8) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 8) (by simp [lowEffect,Effect.components]))))
  have r15 : t3.regValue .r15 = t.regValue .r15 :=
    (e3.agrees.read (n := 64) (r := 15) (by simp [thirdEffect,Effect.components])).trans ((e2.agrees.read (n := 64) (r := 15) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 15) (by simp [lowEffect,Effect.components]))))
  have rcx1 : t1.regValue .rcx = t.regValue .rcx :=
    (e1.agrees.read (n := 64) (r := 1) (by simp [lowEffect,Effect.components]))
  have rcx2 : t2.regValue .rcx = t.regValue .rcx :=
    (e2.agrees.read (n := 64) (r := 1) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 1) (by simp [lowEffect,Effect.components])))
  have v1 := e1.writes.2.2.1
  change t1.regValue .rdi = selectWord (t.regValue .r11) (t.regValue .rdx)
    ((t.regValue .rcx).setWidth 8 |>.setWidth 64) at v1
  have v2 := e2.writes.2.1
  change t2.regValue .rdx = selectWord (t1.regValue .r10) (t1.regValue .rsi)
    ((t1.regValue .rcx).setWidth 8 |>.setWidth 64) at v2
  rw [r10,rsi,rcx1] at v2
  have v3 := e3.writes.2.1
  change t3.regValue .rsi = selectWord (t2.regValue .r9) (t2.regValue .r14)
    ((t2.regValue .rcx).setWidth 8 |>.setWidth 64) at v3
  rw [r9,r14,rcx2] at v3
  have v4 := e4.writes.2.1
  change t4.regValue .rcx = selectWord (t3.regValue .r8) (t3.regValue .r15)
    ((t3.regValue .rcx).setWidth 8 |>.setWidth 64) at v4
  rw [r8,r15,rcx] at v4
  have ptr : t4.regValue .rax = s.regValue .rdi :=
    ((e4.agrees.read (n := 64) (r := 0) (by simp [highEffect,Effect.components])).trans ((e3.agrees.read (n := 64) (r := 0) (by simp [thirdEffect,Effect.components])).trans ((e2.agrees.read (n := 64) (r := 0) (by simp [secondEffect,Effect.components])).trans ((e1.agrees.read (n := 64) (r := 0) (by simp [lowEffect,Effect.components])))))).trans output
  have w1 := (e4.agrees.read (n := 64) (r := 7) (by simp [highEffect,Effect.components])).trans ((e3.agrees.read (n := 64) (r := 7) (by simp [thirdEffect,Effect.components])).trans ((e2.agrees.read (n := 64) (r := 7) (by simp [secondEffect,Effect.components])).trans (v1)))
  have w2 := (e4.agrees.read (n := 64) (r := 2) (by simp [highEffect,Effect.components])).trans ((e3.agrees.read (n := 64) (r := 2) (by simp [thirdEffect,Effect.components])).trans (v2))
  have w3 := (e4.agrees.read (n := 64) (r := 6) (by simp [highEffect,Effect.components])).trans (v3)
  change t4.regValue .rdi = _ at w1
  change t4.regValue .rdx = _ at w2
  change t4.regValue .rsi = _ at w3
  have value : Limbs.mk (t4.regValue .rdi) (t4.regValue .rdx)
      (t4.regValue .rsi) (t4.regValue .rcx) =
      if keep then sumLimbs t else differenceLimbs t := by
    rw [w1,w2,w3,v4,choice]
    cases keep
    · change Limbs.mk (selectWord _ _ 0) (selectWord _ _ 0) (selectWord _ _ 0)
        (selectWord _ _ 0) = differenceLimbs t
      simp only [selectWord_zero]
      rfl
    · change Limbs.mk (selectWord _ _ 1) (selectWord _ _ 1) (selectWord _ _ 1)
        (selectWord _ _ 1) = sumLimbs t
      simp only [selectWord_one]
      rfl
  obtain ⟨n5,u,adv5,final,last,result⟩ := store_output pre.toCalleePre state4 e4.rip ptr value
  refine ⟨n1+n2+n3+n4+n5,u,(((adv1.trans adv2).trans adv3).trans adv4).trans adv5,
    final,last,?_⟩
  cases keep <;> exact result


end P256.Proofs.Signing.Core.Iteration.Components.Addition
