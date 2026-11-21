import P256.Proofs.Sec1.Decompress.Input.Choice
import P256.Proofs.Sec1.Decompress.Input.ZeroMemory
import P256.Proofs.Sec1.Decompress.Input.Prepare
import P256.Proofs.Sec1.Decompress.Input.LimbPre
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.Sec1.Decompress.Cubic (montgomeryAt_of_copy)

structure LimbState [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop extends Frame s t where
  rip : t.RIP = 0x10fd41
  valid : t.regValue .rbp = if x < P256.Spec.Operations.domain.p then 1 else 0
  value : MontgomeryAt t (stackPtr s - 328) (checkedX x)
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  output : (Operand.mem (stackPtr s - 224) : Operand 64).read t = s.regValue .rdi
  r14 : t.regValue .r14 = 0xffffffff00000001

theorem first_select [Bindings] {s v : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} {x : Nat} (pre : Pre s boundary bytes odd)
    (choice : Chosen s v x odd) :
    ∃ fuel t, Advances boundary fuel v t ∧ LimbState s t x odd := by
  obtain ⟨nz,w,rz,readyz,_,ez⟩ := zero_correct boundary pre.outerBoundary v
    (readyToStep choice.machine choice.bindingsSupported) (zero_correct_code choice.loaded) (zero_pre pre.toCalleePre choice.toFrameState choice.rip)
  have framez := zero_frame pre.toCalleePre choice.toFrameState readyz ez
  have hz := zero_value pre.toCalleePre choice.toFrameState ez
  have zeroAddr : stackPtr v+80=stackPtr s-328 := Cubic.input_stack_address choice.rsp (offset := 80) (by decide)
  rw [zeroAddr] at hz
  have cand : MontgomeryAt w (stackPtr s-408) (x % P256.Spec.Operations.domain.p) := by
    apply montgomeryAt_of_copy choice.value
    intro i hi
    have h := zero_byte ez (off := 0) (len := 32) (by decide) (.inl (by decide)) (.inl (by decide)) hi
    simpa only [BitVec.add_zero, choice.rsp] using h
  have signz : (Operand.mem (stackPtr s-332) : Operand 32).read w = BitVec.ofNat 32 odd.toNat := by
    have h := zero_read ez (off := 76) (n := 32) (by decide) (.inr (by decide)) (.inl (by decide))
    have ha : stackPtr v+76=stackPtr s-332 := Cubic.input_stack_address choice.rsp (offset := 76) (by decide)
    change (Operand.mem (stackPtr v+76) : Operand 32).read w = (Operand.mem (stackPtr v+76) : Operand 32).read v at h
    rw [ha] at h
    exact h.trans choice.parity
  have outz : (Operand.mem (stackPtr s-224) : Operand 64).read w = s.regValue .rdi := by
    have h := zero_read ez (off := 184) (n := 64) (by decide) (.inr (by decide)) (.inr (by decide))
    have ha : stackPtr v+184=stackPtr s-224 := Cubic.input_stack_address choice.rsp (offset := 184) (by decide)
    change (Operand.mem (stackPtr v+184) : Operand 64).read w = (Operand.mem (stackPtr v+184) : Operand 64).read v at h
    rw [ha] at h
    exact h.trans choice.output
  obtain ⟨np,p,rp,readyp,_,ep⟩ := prepare_correct boundary pre.outerBoundary w readyz
    (programText_slice (programLoaded_codeIn framez.loaded) 0xfd24 prepareBytes (by decide +kernel) (by decide +kernel)) ez.rip
  have framep := framez.after_registers readyp ep.agrees
    (by simp [prepareEffect, Effect.components, Component.Covers]) (by simp [prepareEffect, Effect.components])
  have memp := ep.agrees.external (by simp [prepareEffect, Effect.components, Component.Covers])
  obtain ⟨entry,rc,readyc,ec⟩ := ScalarFrame.scalar_call pre.toCalleePre (by decide) (by decide) framep 0xfd3c 0x947f
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x191c0 (by decide)) ep.rip
  change (callEffect (fun _ => 0x1191c0) 0x10fd41 p).Holds p entry at ec
  have framec := ScalarFrame.FrameState.after_call pre.toCalleePre (by decide) (by decide) framep readyc ec
  have ret : (returnBoundary entry).rip=0x10fd41 := (callEffect_stack ec).1
  have dest : entry.regValue .rdi=stackPtr s-328 := by
    have h := (ec.agrees.read (n := 64) (r := 7) (by simp)).trans ep.writes.2.1
    exact h.trans (Cubic.input_stack_address framez.rsp (offset := 80) (by decide))
  have src : entry.regValue .rdx=stackPtr s-408 := by
    exact ((ec.agrees.read (n := 64) (r := 2) (by simp)).trans ep.writes.2.2.2.2.1).trans
      ((ez.agrees.read (n := 64) (r := 15) (by simp [zeroEffect, Effect.components])).trans choice.r15)
  have cp := select_call_pre pre.toCalleePre framec framec.rsp ec.rip
    ((ec.agrees.read (n := 64) (r := 6) (by simp)).trans ep.writes.2.2.1)
    ((ec.agrees.read (n := 64) (r := 1) (by simp)).trans ep.writes.2.2.2.1)
    src dest (ret ▸ inProgram_of_textOffset 0xfd41 (by decide))
  have al : (Operand.reg 0 : Operand 8).read w = if x < P256.Spec.Operations.domain.p then 1 else 0 :=
    by
      have h := congrArg (fun v : BitVec 64 => v.setWidth 8) choice.valid
      change (Operand.reg 0 : Operand 8).read v = _ at h
      have h' := (ez.agrees.read (n := 8) (r := 0) (by simp [zeroEffect, Effect.components])).trans h
      by_cases hx : x < P256.Spec.Operations.domain.p
      · simpa [hx] using h'
      · simpa [hx] using h'
  have rbp : entry.regValue .rbp = if x < P256.Spec.Operations.domain.p then 1 else 0 := by
    have h := (ec.agrees.read (n := 64) (r := 5) (by simp)).trans ep.writes.1
    change entry.regValue .rbp = ((Operand.reg 0 : Operand 8).read w).setWidth 64 at h
    rw [h, al]
    split <;> rfl
  have r8 : entry.regValue .r8 = if decide (x < P256.Spec.Operations.domain.p) then 1 else 0 := by
    have h := (ec.agrees.read (n := 64) (r := 8) (by simp)).trans ep.writes.2.2.2.2.2
    change entry.regValue .r8 = ((Operand.reg 0 : Operand 8).read w).setWidth 64 at h
    rw [h, al]
    by_cases hx : x < P256.Spec.Operations.domain.p <;> simp [hx]
  have callCopy {off : Nat} {x : Nat} (ho : off ≤ 408) (hl : 32 ≤ off+8)
      (h : MontgomeryAt w (stackPtr s-BitVec.ofNat 64 off) x) :
      MontgomeryAt entry (stackPtr s-BitVec.ofNat 64 off) x := by
    apply montgomeryAt_of_copy h
    intro i hi
    exact (ScalarFrame.scalar_call_byte (by decide) framep ec ho hl hi).trans (by rw [memp])
  have zeroC := callCopy (off := 328) (by decide) (by decide) hz
  have candC := callCopy (off := 408) (by decide) (by decide) cand
  obtain ⟨t,result,bytes⟩ := LimbSelect.limb_select32_correct cp r8
  have framet := stack_result_frame pre framec dest (by decide) (by decide) (by decide) result
  have value : MontgomeryAt t (stackPtr s-328) (checkedX x) := by
    by_cases hc : x < P256.Spec.Operations.domain.p
    · have hcand : MontgomeryAt entry (stackPtr s-408) (x) := by
        simpa only [BitVec.ofNat_eq_ofNat, Nat.mod_eq_of_lt hc] using candC
      simp only [checkedX, hc, ite_true]
      apply montgomeryAt_of_copy hcand
      intro i hi
      have hb := bytes i hi
      simpa only [BitVec.ofNat_eq_ofNat, hc, decide_true, Bool.true_eq, ite_true, dest, src] using hb
    · have hz' : MontgomeryAt t (stackPtr s-328) 0 := by
        apply montgomeryAt_of_copy zeroC
        intro i hi
        have hb := bytes i hi
        simpa only [BitVec.ofNat_eq_ofNat, hc, decide_false, Bool.false_eq_true, ite_false, dest] using hb
      simpa only [checkedX, hc, ite_false] using hz'
  obtain ⟨m, rr⟩ := result.execution
  refine ⟨nz+np+1+m, t, ((rz.trans rp).trans rc).trans rr,
    ⟨framet, result.rip.trans ret, (result.calleeSaved .rbp (by simp)).trans rbp, value, ?_, ?_, ?_⟩⟩
  · have h1 := stack_result_read pre framec.rsp dest result (by decide) (offset := 332) (n := 32) (by decide) (by decide) (.inr (by decide))
    have h2 := ScalarFrame.scalar_call_read (by decide) framep ec (offset := 332) (n := 32) (by decide) (by decide)
    exact h1.trans (h2.trans (by change memLoad p.external _ _ = _; rw [memp]; exact signz))
  · have h1 := stack_result_read pre framec.rsp dest result (by decide) (offset := 224) (n := 64) (by decide) (by decide) (.inl (by decide))
    have h2 := ScalarFrame.scalar_call_read (by decide) framep ec (offset := 224) (n := 64) (by decide) (by decide)
    exact h1.trans (h2.trans (by change memLoad p.external _ _ = _; rw [memp]; exact outz))
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((ec.agrees.read (n := 64) (r := 14) (by simp)).trans
        ((ep.agrees.read (n := 64) (r := 14) (by simp [prepareEffect, Effect.components])).trans
          ((ez.agrees.read (n := 64) (r := 14) (by simp [zeroEffect, Effect.components])).trans choice.r14)))

end P256.Proofs.Sec1.Decompress.Input
