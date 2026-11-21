import P256.Proofs.Generate.Sampler.Draw
import P256.Proofs.Generate.Sampler.Next
import P256.Proofs.Generate.Sampler.Nonzero.Correct
import P256.Proofs.Generate.Model.Value

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar

theorem trace_finish [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset d : Nat} (pre : Pre s boundary input)
    (trace : DrawTrace input offset d) {t : RamState} (state : ReadReady s t input offset) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ State s u ∧ u.RIP = 0x100d1d ∧
      Nat256At u (stackPtr s-256) d ∧
      memLoad u.external (stackPtr s-192) 64 = s.regValue .rdi := by
  induction trace generalizing t with
  | @accept offset d available decoded =>
    obtain ⟨size,positive,below,value⟩ := decodeSecret_some_iff.mp decoded
    obtain ⟨a,⟨na,ha⟩,sa,remaining,scalar⟩ := draw pre state available
    rw [value] at sa scalar
    have branch : LoopReady s a input offset 0x100c00 32 := by
      simpa only [ite_eq_left below] using sa
    obtain ⟨u,⟨nb,hb⟩,su⟩ := Nonzero.correct pre branch scalar remaining available
    rw [ite_eq_right (by omega : ¬ d=0)] at su
    exact ⟨u,⟨_,ha.trans hb⟩,su⟩
  | @reject offset d available decoded rest ih =>
    obtain ⟨a,⟨na,ha⟩,sa,remaining,scalar⟩ := draw pre state available
    by_cases below : Arith.uint (input.extract offset (offset+32)) < Operations.domain.n
    · have zero : Arith.uint (input.extract offset (offset+32)) = 0 := by
        by_cases nonzero : Arith.uint (input.extract offset (offset+32)) = 0
        · exact nonzero
        apply False.elim
        have accepted := decodeSecret_some_iff.mpr
          ⟨chunk_size available,by omega,below,rfl⟩
        rw [decoded] at accepted
        cases accepted
      have branch : LoopReady s a input offset 0x100c00 32 := by
        simpa only [ite_eq_left below] using sa
      obtain ⟨b,⟨nb,hb⟩,sb⟩ := Nonzero.correct pre branch scalar remaining available
      rw [ite_eq_left zero] at sb
      obtain ⟨c,⟨nc,hc⟩,sc⟩ := first_read pre sb rest.available
      obtain ⟨u,⟨nd,hd⟩,su,rip,value,pointer⟩ := ih sc
      exact ⟨u,⟨_,((ha.trans hb).trans hc).trans hd⟩,su,rip,value,pointer⟩
    · have branch : LoopReady s a input offset 0x100ce5 32 := by
        simpa only [ite_eq_right below] using sa
      obtain ⟨b,⟨nb,hb⟩,sb⟩ := next_read pre branch remaining rest.available
      obtain ⟨u,⟨nc,hc⟩,su,rip,value,pointer⟩ := ih sb
      exact ⟨u,⟨_,(ha.trans hb).trans hc⟩,su,rip,value,pointer⟩

end P256.Proofs.Generate.Sampler
