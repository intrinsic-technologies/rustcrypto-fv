import P256.Proofs.Generate.Scalar.Compare.Low
import P256.Proofs.Generate.Scalar.Compare.Second
import P256.Proofs.Generate.Scalar.Compare.Third
import P256.Proofs.Generate.Scalar.Compare.High
import P256.Proofs.Generate.Scalar.Compare.Validity
import P256.Proofs.Generate.Scalar.Compare.Arithmetic

open P256.Proofs.SecretKeyFromBytes.Scalar (orderBorrow orderBorrow_validity)

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

theorem compare_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pre : ComparePre 0x112efb s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      ComparePre 0x112fa6 t ∧ AgreesExcept (compareFrame s) s t ∧
      t.regValue .rdi = if (compareInput s).toNat < P256.Spec.Operations.domain.n then 1 else 0 :=
        by
  obtain ⟨n0, t0, run0, rd0, ld0, p0, f0, zero0, low0⟩ := low_correct hout ready loaded pre
  obtain ⟨n1, t1, run1, rd1, ld1, p1, h1, f1⟩ :=
    compare_run (s := t0) (q := 0x112f49) (offset := 0x12f2c)
      (second_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd0 ld0 p0 p0.rip rfl
      (by simp [secondWordEffect, Effect.components, compareFrame])
  have g1 := compare_trans f0 f1
  obtain ⟨n2, t2, run2, rd2, ld2, p2, h2, f2⟩ :=
    compare_run (s := t1) (q := 0x112f6c) (offset := 0x12f49)
      (third_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd1 ld1 p1 p1 rfl
      (by simp [thirdEffect, Effect.components, compareFrame])
  have g2 := compare_trans g1 f2
  obtain ⟨n3, t3, run3, rd3, ld3, p3, h3, f3⟩ :=
    compare_run (s := t2) (q := 0x112f97) (offset := 0x12f6c)
      (high_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd2 ld2 p2 p2 rfl
      (by simp [highWordEffect, Effect.components, compareFrame])
  have g3 := compare_trans g2 f3
  obtain ⟨n4, t4, run4, rd4, ld4, p4, h4, f4⟩ :=
    compare_run (s := t3) (q := 0x112fa6) (offset := 0x12f97)
      (validity_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd3 ld3 p3 p3 rfl
      (by simp [validityEffect, Effect.components, compareFrame])
  have x1 : t0.regValue .r12 = s.regValue .r12 :=
    f0.read (n := 64) (r := 12) (by simp [compareFrame])
  have x2 : t1.regValue .r15 = s.regValue .r15 :=
    g1.read (n := 64) (r := 15) (by simp [compareFrame])
  have x3 : t2.regValue .r14 = s.regValue .r14 :=
    g2.read (n := 64) (r := 14) (by simp [compareFrame])
  have zero2 : t2.regValue .rcx = 0 :=
    ((h1.agrees.trans h2.agrees).read (n := 64) (r := 1)
      (by simp [secondWordEffect, thirdEffect, Effect.components])).trans zero0
  have w1 := h1.writes.2
  change t1.regValue .rdx = (~~~t0.regValue .r12 |||
    (0x4319055258e8617c + t0.regValue .r12 + t0.regValue .rdx)) >>> 63 at w1
  rw [x1, low0] at w1
  have w2 := h2.writes.2.2
  change t2.regValue .rsi = (~~~t1.regValue .r15 |||
    ((-t1.regValue .rdx).sshiftRight 63 + t1.regValue .r15 + 1)) >>> 63 at w2
  rw [x2, w1] at w2
  have w2 := w2.trans (congrArg
    (fun r : BitVec 64 => (~~~s.regValue .r15 ||| r) >>> 63)
    (third_word_shift_eq _ _))
  have w3 := h3.writes.2.2.2
  change t3.regValue .rsi = (0x100000000 + t2.regValue .r14 +
    (t2.regValue .rcx - t2.regValue .rsi).sshiftRight 63 ||| ~~~t2.regValue .r14) >>> 63 at w3
  have zero_sub (x : BitVec 64) : (0 : BitVec 64) - x = -x := BitVec.zero_sub x
  rw [x3, zero2, w2, zero_sub] at w3
  have wb : t3.regValue .rsi = orderBorrow (compareInput s) := by
    simpa only [orderBorrow, compareInput, BitVec.or_comm] using w3
  have w4 := h4.writes.2.2
  change t4.regValue .rdi = ((t3.regValue .rsi).setWidth 8 &&& 1).setWidth 64 at w4
  rw [wb, orderBorrow_validity] at w4
  exact ⟨n0+n1+n2+n3+n4, t4, (((run0.trans run1).trans run2).trans run3).trans run4,
    rd4, ld4, p4, compare_trans g3 f4, w4⟩

end P256.Proofs.Generate.Scalar
