import P256.Proofs.Sec1.Affine.Uncompressed.Parse.ConversionCall
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.ChoiceCall
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Memory
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.YConversionArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.XConversionArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.YChoiceArgument
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks.XChoiceArgument

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open Blocks

theorem y_converted [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110704) (raw : Nat256At t (stackPtr s-592) x)
    (valid : (Operand.reg 14 : Operand 64).read t = if x < Operations.domain.p then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110739 ∧
      u.regValue .rax = (if x < Operations.domain.p then 1 else 0) ∧
      MontgomeryAt u (stackPtr s-744) (x % Operations.domain.p) ∧
      u.regValue .rbx = t.regValue .rbx ∧
      u.regValue .rbp = t.regValue .rsi ∧
      u.regValue .r12 = t.regValue .r12 ∧
      u.regValue .r13 = t.regValue .r13 ∧
      u.regValue .r14 = t.regValue .r14 ∧
      u.regValue .r15 = t.regValue .r15 ∧
      (∀ off len : Nat, off ≤ 760 → len ≤ off+8 →
        (off+32 ≤ 744 ∨ 744+len ≤ off) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  obtain ⟨na,a,ra,readya,_,ea⟩ := y_conversion_arguments_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10704 yConversionArgumentsBytes
      (by decide) (by decide +kernel)) rip
  have fa := state.after_registers readya ea.agrees
    (by simp [yConversionArgumentsEffect, Effect.components, Component.Covers])
    (by simp [yConversionArgumentsEffect, Effect.components])
  have ma := ea.agrees.external (by simp [yConversionArgumentsEffect, Effect.components, Component.Covers])
  have source : a.regValue .rsi = stackPtr s-592 :=
    ea.writes.2.2.2.2.1.trans (stack_address state (by decide))
  have output : a.regValue .rdi = stackPtr s-744 :=
    ea.writes.1.trans (stack_address state (by decide))
  have rawA : Nat256At a (stackPtr s-592) x := ⟨raw.1, fun i hi => by rw [ma]; exact raw.2 i hi⟩
  obtain ⟨nc,c,rc,fc,ic,valuec,abi,kept,_⟩ := conversion_call pre fa 0x1072b 0xffff8840
    (by decide) (by decide +kernel) (by decide) ea.rip source output rawA
    ea.writes.2.2.2.2.2.1
    ea.writes.2.2.2.2.2.2 ea.writes.2.2.1
  have vc : (Operand.reg 14 : Operand 64).read c = if x < Operations.domain.p then 1 else 0 :=
    (abi .r14 (by simp)).trans
      ((ea.agrees.read (n := 64) (r := 14) (by simp [yConversionArgumentsEffect, Effect.components])).trans valid)
  obtain ⟨nb,b,rb,readyb,_,eb⟩ := y_choice_argument_correct boundary pre.outerBoundary c
    (readyToStep fc.machine fc.bindingsSupported)
    (programText_slice (programLoaded_codeIn fc.loaded) 0x10730 yChoiceArgumentBytes
      (by decide) (by decide +kernel)) ic
  have fb := fc.after_registers readyb eb.agrees
    (by simp [yChoiceArgumentEffect, Effect.components, Component.Covers])
    (by simp [yChoiceArgumentEffect, Effect.components])
  have mb := eb.agrees.external (by simp [yChoiceArgumentEffect, Effect.components, Component.Covers])
  obtain ⟨nu,u,ru,fu,iu,vu,gu⟩ := Choice.choice_call pre.toCalleePre fb 0x10734 0x8937
    (by decide) (by decide +kernel) (by decide) eb.rip
  have saved (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      u.regValue r = a.regValue r := by
    apply Eq.trans ?_ (abi r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (gu.read (n := 64) (r := 3) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 3) (by simp [yChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 5) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 5) (by simp [yChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 12) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 12) (by simp [yChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 13) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 13) (by simp [yChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 14) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 14) (by simp [yChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 15) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 15) (by simp [yChoiceArgumentEffect, Effect.components]))
  refine ⟨na+nc+nb+nu,u,((ra.trans rc).trans rb).trans ru,fu,iu,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have h := eb.writes
    change (Operand.reg 7 : Operand 64).read b = (((Operand.reg 14 : Operand 64).read c).setWidth 8).setWidth 64 at h
    have low := congrArg (fun x : BitVec 64 => x.setWidth 8) h
    change (Operand.reg 7 : Operand 8).read b = _ at low
    rw [low,vc] at vu
    change (Operand.reg 0 : Operand 64).read u = _
    by_cases hx : x < Operations.domain.p <;> simpa [hx] using vu
  · apply valuec.of_bytes_eq
    intro i hi
    have h := Choice.byte_preserved gu (offset := 744) (len := 32) (by decide) (by decide) hi
    rw [mb] at h
    exact h
  · exact (saved .rbx (by simp)).trans (ea.agrees.read (n := 64) (r := 3) (by simp [yConversionArgumentsEffect, Effect.components]))
  · exact (saved .rbp (by simp)).trans ea.writes.2.2.2.1
  · exact (saved .r12 (by simp)).trans (ea.agrees.read (n := 64) (r := 12) (by simp [yConversionArgumentsEffect, Effect.components]))
  · exact (saved .r13 (by simp)).trans (ea.agrees.read (n := 64) (r := 13) (by simp [yConversionArgumentsEffect, Effect.components]))
  · exact (saved .r14 (by simp)).trans (ea.agrees.read (n := 64) (r := 14) (by simp [yConversionArgumentsEffect, Effect.components]))
  · exact (saved .r15 (by simp)).trans (ea.agrees.read (n := 64) (r := 15) (by simp [yConversionArgumentsEffect, Effect.components]))
  · intro off len ho hl apart i hi
    rw [Choice.byte_preserved gu ho hl hi,mb,kept off len ho hl apart i hi,ma]

theorem x_converted [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x1108d8) (raw : Nat256At t (stackPtr s-592) x)
    (valid : (Operand.reg 5 : Operand 64).read t = if x < Operations.domain.p then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11090a ∧
      u.regValue .rax = (if x < Operations.domain.p then 1 else 0) ∧
      MontgomeryAt u (stackPtr s-744) (x % Operations.domain.p) ∧
      u.regValue .rbx = t.regValue .rbx ∧
      u.regValue .rbp = t.regValue .rbp ∧
      u.regValue .r12 = stackPtr s-744 ∧
      u.regValue .r13 = t.regValue .r13 ∧
      u.regValue .r14 = t.regValue .r14 ∧
      u.regValue .r15 = t.regValue .r15 ∧
      (∀ off len : Nat, off ≤ 760 → len ≤ off+8 →
        (off+32 ≤ 744 ∨ 744+len ≤ off) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  obtain ⟨na,a,ra,readya,_,ea⟩ := x_conversion_arguments_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x108d8 xConversionArgumentsBytes
      (by decide) (by decide +kernel)) rip
  have fa := state.after_registers readya ea.agrees
    (by simp [xConversionArgumentsEffect, Effect.components, Component.Covers])
    (by simp [xConversionArgumentsEffect, Effect.components])
  have ma := ea.agrees.external (by simp [xConversionArgumentsEffect, Effect.components, Component.Covers])
  have source : a.regValue .rsi = stackPtr s-592 :=
    ea.writes.2.1.trans (stack_address state (by decide))
  have output : a.regValue .rdi = stackPtr s-744 :=
    ea.writes.2.2.2.1.trans (stack_address state (by decide))
  have rawA : Nat256At a (stackPtr s-592) x := ⟨raw.1, fun i hi => by rw [ma]; exact raw.2 i hi⟩
  obtain ⟨nc,c,rc,fc,ic,valuec,abi,kept,_⟩ := conversion_call pre fa 0x108fc 0xffff866f
    (by decide) (by decide +kernel) (by decide) ea.rip source output rawA
    ea.writes.2.2.2.2.1
    ea.writes.2.2.2.2.2 ea.writes.2.2.1
  have vc : (Operand.reg 5 : Operand 64).read c = if x < Operations.domain.p then 1 else 0 :=
    (abi .rbp (by simp)).trans
      ((ea.agrees.read (n := 64) (r := 5) (by simp [xConversionArgumentsEffect, Effect.components])).trans valid)
  obtain ⟨nb,b,rb,readyb,_,eb⟩ := x_choice_argument_correct boundary pre.outerBoundary c
    (readyToStep fc.machine fc.bindingsSupported)
    (programText_slice (programLoaded_codeIn fc.loaded) 0x10901 xChoiceArgumentBytes
      (by decide) (by decide +kernel)) ic
  have fb := fc.after_registers readyb eb.agrees
    (by simp [xChoiceArgumentEffect, Effect.components, Component.Covers])
    (by simp [xChoiceArgumentEffect, Effect.components])
  have mb := eb.agrees.external (by simp [xChoiceArgumentEffect, Effect.components, Component.Covers])
  obtain ⟨nu,u,ru,fu,iu,vu,gu⟩ := Choice.choice_call pre.toCalleePre fb 0x10905 0x8766
    (by decide) (by decide +kernel) (by decide) eb.rip
  have saved (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      u.regValue r = a.regValue r := by
    apply Eq.trans ?_ (abi r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (gu.read (n := 64) (r := 3) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 3) (by simp [xChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 5) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 5) (by simp [xChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 12) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 12) (by simp [xChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 13) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 13) (by simp [xChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 14) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 14) (by simp [xChoiceArgumentEffect, Effect.components]))
    · exact (gu.read (n := 64) (r := 15) (by simp [Choice.components])).trans
        (eb.agrees.read (n := 64) (r := 15) (by simp [xChoiceArgumentEffect, Effect.components]))
  refine ⟨na+nc+nb+nu,u,((ra.trans rc).trans rb).trans ru,fu,iu,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have h := eb.writes
    change (Operand.reg 7 : Operand 64).read b = (((Operand.reg 5 : Operand 64).read c).setWidth 8).setWidth 64 at h
    have low := congrArg (fun x : BitVec 64 => x.setWidth 8) h
    change (Operand.reg 7 : Operand 8).read b = _ at low
    rw [low,vc] at vu
    change (Operand.reg 0 : Operand 64).read u = _
    by_cases hx : x < Operations.domain.p <;> simpa [hx] using vu
  · apply valuec.of_bytes_eq
    intro i hi
    have h := Choice.byte_preserved gu (offset := 744) (len := 32) (by decide) (by decide) hi
    rw [mb] at h
    exact h
  · exact (saved .rbx (by simp)).trans (ea.agrees.read (n := 64) (r := 3) (by simp [xConversionArgumentsEffect, Effect.components]))
  · exact (saved .rbp (by simp)).trans (ea.agrees.read (n := 64) (r := 5) (by simp [xConversionArgumentsEffect, Effect.components]))
  · exact (saved .r12 (by simp)).trans (ea.writes.1.trans (stack_address state (by decide)))
  · exact (saved .r13 (by simp)).trans (ea.agrees.read (n := 64) (r := 13) (by simp [xConversionArgumentsEffect, Effect.components]))
  · exact (saved .r14 (by simp)).trans (ea.agrees.read (n := 64) (r := 14) (by simp [xConversionArgumentsEffect, Effect.components]))
  · exact (saved .r15 (by simp)).trans (ea.agrees.read (n := 64) (r := 15) (by simp [xConversionArgumentsEffect, Effect.components]))
  · intro off len ho hl apart i hi
    rw [Choice.byte_preserved gu ho hl hi,mb,kept off len ho hl apart i hi,ma]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
