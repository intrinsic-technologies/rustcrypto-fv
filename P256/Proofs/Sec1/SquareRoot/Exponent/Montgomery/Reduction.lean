import P256.Proofs.Field.Representation
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Select

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Pre [Bindings] (entry : BitVec 64) (boundary : ReturnBoundary)
    (s : RamState) (a : Limbs) (high : BitVec 64) : Prop where
  entryValid : Entry entry
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  outerBoundary : ¬ InProgram boundary.rip
  memory : MemoryPre s
  rip : s.RIP = entry + 0x430#64
  input : Input s a high
  modulus : Modulus s modulus
  bound : a.toNat + 2^256 * high.toNat < 2 * P256.Spec.Operations.domain.p

structure Result [Bindings] (entry : BitVec 64) (boundary : ReturnBoundary)
    (s t : RamState) (value : Nat) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = entry + 0x5ab#64
  rsp : stackPtr t = stackPtr s
  rdi : t.regValue .rdi = s.regValue .rdi
  frame : AgreesExcept (components s) s t
  output : Nat256At t (s.regValue .rdi) (P256.Proofs.Field.Montgomery.subtractP value)

theorem reduction_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {a : Limbs} {high : BitVec 64} (pre : Pre entry boundary s a high) :
    ∃ t, Result entry boundary s t (a.toNat + 2^256 * high.toNat) := by
  obtain ⟨n, t, run1, ready1, loaded1, rip1, input1, difference1, memory1, frame1, _, rdi1⟩ :=
    borrow_correct pre.entryValid pre.ready pre.loaded pre.outerBoundary pre.memory pre.rip
      pre.input pre.modulus
  have hb := P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one (subRaw_toNat a modulus).1
  obtain ⟨m, u, run2, ready2, loaded2, rip2, output, frame2⟩ :=
    select_correct pre.entryValid ready1 loaded1 pre.outerBoundary memory1 rip1 input1 difference1 hb
  have frame := scratch_then_components frame1 frame2
  change Nat256At u (t.regValue .rdi) (reduce a high).toNat at output
  rw [rdi1, reduce_toNat a high pre.bound] at output
  exact ⟨u, ⟨n+m, run1.trans run2⟩, ready2, loaded2, rip2,
    components_rsp frame, components_rdi frame, frame, output⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
