import P256.Proofs.Sec1.SquareRoot.Exponent.LoopControl
import P256.Proofs.Sec1.SquareRoot.Exponent.Preservation

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ExponentLoopState.window_begin [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x n : Nat} (hctx : ExponentPre s boundary x)
    (h : ExponentLoopState s t x (n + 1)) (hn : n < 64) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentPosition s u x n ∧
      u.RIP = (if n = 63 then 0x11586c else 0x1154d6) ∧
      MontgomeryAt u (exponentFrameBase s + 0x30)
        (x ^ (sqrtExponent / 16 ^ (n + 1)) % P256.Spec.Operations.domain.p) := by
  obtain ⟨u, fuel, ha, hr, hip, hw, hag⟩ := exponent_window_begin
    (readyToStep h.frame.machine h.frame.bindingsSupported) (programLoaded_codeIn h.frame.loaded)
    h.rip hctx.outerBoundary
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (hag.external (by simp [Component.Covers]))
  have hp : ExponentPosition s u x n := by
    refine ⟨h.frame.of_registers hr hag (by decide) (by simp [Component.Covers]),
      h.constants.of_memory he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hword := h.word
      change (Operand.reg 5 : Operand 64).read t = _ at hword
      exact (hag.read (n := 64) (r := 5) (by decide)).trans (by
        simpa only [Nat.add_sub_cancel] using hword)
    · exact exponentWordAt_of_memory he (by simpa only [Nat.add_sub_cancel] using h.savedWord)
    · change (Operand.reg 14 : Operand 64).read u = _
      rw [hw]
      have hwindow : (Operand.reg 14 : Operand 32).read t =
          BitVec.ofNat 32 (n % 16 + 1) := by
        change (t.regValue .r14).setWidth 32 = _
        rw [h.window, Nat.add_sub_cancel, BitVec.setWidth_ofNat_of_le (by decide)]
      rw [hwindow]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat]
      omega
    · exact (hag.read (n := 64) (r := 3) (by decide)).trans h.firstWord
    · exact (hag.read (n := 64) (r := 13) (by decide)).trans h.firstWindow
    · exact (hag.read (n := 64) (r := 15) (by decide)).trans h.parameterPointer
    · exact (hag.read (n := 64) (r := 11) (by decide)).trans h.modulus0
    · exact (hag.read (n := 64) (r := 12) (by decide)).trans h.inverse
  refine ⟨u, fuel, ha, hp, ?_, montgomeryAt_of_memory he h.accumulator⟩
  rw [hip, h.skips_squares (by omega) (by omega)]
  simp only [decide_eq_true_eq, show n + 1 = 64 ↔ n = 63 by omega]

theorem ExponentPosition.of_flags [Bindings] {s t u : RamState} {x n : Nat}
    (h : ExponentPosition s t x n) (hr : ReadyToStep u)
    (ha : AgreesExcept [.flags, .rip] t u) : ExponentPosition s u x n := by
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (ha.external (by simp [Component.Covers]))
  exact ⟨h.frame.of_registers hr ha (by decide) (by simp [Component.Covers]),
    h.constants.of_memory he,
    (ha.read (n := 64) (r := 5) (by decide)).trans h.word,
    exponentWordAt_of_memory he h.savedWord,
    (ha.read (n := 64) (r := 14) (by decide)).trans h.window,
    (ha.read (n := 64) (r := 3) (by decide)).trans h.firstWord,
    (ha.read (n := 64) (r := 13) (by decide)).trans h.firstWindow,
    (ha.read (n := 64) (r := 15) (by decide)).trans h.parameterPointer,
    (ha.read (n := 64) (r := 11) (by decide)).trans h.modulus0,
    (ha.read (n := 64) (r := 12) (by decide)).trans h.inverse⟩

theorem ExponentPosition.window32 [Bindings] {s t : RamState} {x n : Nat}
    (h : ExponentPosition s t x n) :
    (Operand.reg 14 : Operand 32).read t = BitVec.ofNat 32 (n % 16) := by
  change (t.regValue .r14).setWidth 32 = _
  rw [h.window, BitVec.setWidth_ofNat_of_le (by decide)]

theorem ExponentPosition.finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} (hctx : ExponentPre s boundary x) (h : ExponentPosition s t x 0)
    (hip : t.RIP = 0x1154c0)
    (hacc : MontgomeryAt t (exponentFrameBase s + 0x30)
      (x ^ sqrtExponent % P256.Spec.Operations.domain.p)) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFinishState s u x := by
  obtain ⟨u, fuel, had, hr, hiu, hag⟩ := exponent_window_continue
    (readyToStep h.frame.machine h.frame.bindingsSupported) (programLoaded_codeIn h.frame.loaded)
    hip hctx.outerBoundary
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (hag.external (by simp [Component.Covers]))
  have hp := h.of_flags hr hag
  refine ⟨u, fuel, had, hp.frame, ?_,
    montgomeryAt_of_memory he hacc⟩
  have hw : (Operand.reg 5 : Operand 64).read t = 0 := h.word
  have h12 : (Operand.reg 14 : Operand 32).read t = 0 := h.window32
  rw [h12, hw, ite_eq_left rfl, ite_eq_left rfl] at hiu
  exact hiu

theorem ExponentPosition.continue_window [Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {x n : Nat} (hctx : ExponentPre s boundary x)
    (h : ExponentPosition s t x n) (hn : n % 16 ≠ 0) (hip : t.RIP = 0x1154c0)
    (hacc : MontgomeryAt t (exponentFrameBase s + 0x30)
      (x ^ (sqrtExponent / 16 ^ n) % P256.Spec.Operations.domain.p)) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentLoopState s u x n := by
  obtain ⟨u, fuel, had, hr, hiu, hag⟩ := exponent_window_continue
    (readyToStep h.frame.machine h.frame.bindingsSupported) (programLoaded_codeIn h.frame.loaded)
    hip hctx.outerBoundary
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (hag.external (by simp [Component.Covers]))
  have hp := h.of_flags hr hag
  have hindex : (n - 1) / 16 = n / 16 ∧ (n - 1) % 16 + 1 = n % 16 := by omega
  have hnword : (Operand.reg 14 : Operand 32).read t ≠ 0 := by
    rw [h.window32]
    intro hzero
    have hz := congrArg BitVec.toNat hzero
    change (n % 16) % 4294967296 = 0 at hz
    omega
  refine ⟨u, fuel, had, hp.frame, hp.constants, ?_, ?_, ?_, ?_,
    hp.firstWord, hp.firstWindow, hp.parameterPointer, hp.modulus0, hp.inverse,
    montgomeryAt_of_memory he hacc⟩
  · simpa only [hnword, ite_false] using hiu
  · rw [hindex.1]; exact hp.word
  · rw [hindex.1]; exact hp.savedWord
  · rw [hindex.2]; exact hp.window

end P256.Proofs.Sec1.SquareRoot
