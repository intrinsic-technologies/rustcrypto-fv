import P256.Proofs.Sec1.SquareRoot.Exponent.State
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

open P256.Proofs.Common.Machine
open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponentWordAt_of_memory {s t : RamState} {a v : BitVec 64}
    (h : ∀ address : BitVec 64, t.external[address]? = s.external[address]?)
    (hv : exponentWordAt s a v) : exponentWordAt t a v := by
  apply Eq.trans _ hv
  apply memLoad_congr
  intro i hi
  change (t.external[a + BitVec.ofNat 64 i]?).getD 0 = _
  rw [h]
  rfl

theorem nat256At_of_memory {s t : RamState} {a : BitVec 64} {x : Nat}
    (h : ∀ address : BitVec 64, t.external[address]? = s.external[address]?)
    (hv : Nat256At s a x) : Nat256At t a x :=
  ⟨hv.1, fun i hi => (h _).trans (hv.2 i hi)⟩

theorem montgomeryAt_of_memory {s t : RamState} {a : BitVec 64} {x : Nat}
    (h : ∀ address : BitVec 64, t.external[address]? = s.external[address]?)
    (hv : MontgomeryAt s a x) : MontgomeryAt t a x :=
  ⟨hv.1, nat256At_of_memory h hv.2⟩

theorem parametersAt_of_memory {s t : RamState} {a : BitVec 64}
    (h : ∀ address : BitVec 64, t.external[address]? = s.external[address]?)
    (hv : ParametersAt s a) : ParametersAt t a :=
  fun i hi => (h _).trans (hv i hi)

theorem residueAt_of_memory {s t : RamState} {a : BitVec 64} {x : Nat}
    (h : ∀ address : BitVec 64, t.external[address]? = s.external[address]?)
    (hv : ResidueAt s a x) : ResidueAt t a x :=
  ⟨montgomeryAt_of_memory h hv.1, parametersAt_of_memory h hv.2⟩

theorem ExponentFrame.of_registers [Bindings] {s t u : RamState} {cs : List Component}
    (h : ExponentFrame s t) (hr : ReadyToStep u) (ha : AgreesExcept cs t u)
    (hsp : .reg 4 ∉ cs) (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    ExponentFrame s u := by
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (ha.external hm)
  refine ⟨?_, supportedMachine_of_ready_agrees h.machine hr ha,
    bindingsSupported_of_ready_agrees h.bindingsSupported hr ha,
    ha.directionFlagClear (by component_not_mem) h.directionFlag, ?_, ?_, ?_, ?_,
    fun a hp => ha.grow a (h.allocated a hp),
    exponentWordAt_of_memory he h.returnAddress,
    fun i hi => exponentWordAt_of_memory he (h.saved i hi),
    exponentWordAt_of_memory he h.outputPointer⟩
  · exact (ha.read (n := 64) hsp).trans h.rsp
  · exact (ha.mxcsr (by component_not_mem)).trans h.mxcsr
  · exact (ha.fcw (by component_not_mem)).trans h.fp87
  · intro a hab
    exact (he a).trans (h.frame a hab)
  · intro a b hab
    exact (he a).trans (h.loaded a b hab)

theorem ExponentConstants.of_memory {s t u : RamState} {x : Nat}
    (h : ExponentConstants s t x)
    (he : ∀ address : BitVec 64, u.external[address]? = t.external[address]?) :
    ExponentConstants s u x := by
  refine ⟨residueAt_of_memory he h.input,
    fun i hi => montgomeryAt_of_memory he (h.table i hi),
    nat256At_of_memory he h.exponent, ?_,
    exponentWordAt_of_memory he h.modulus0,
    exponentWordAt_of_memory he h.modulus1,
    exponentWordAt_of_memory he h.modulus2,
    exponentWordAt_of_memory he h.modulus3,
    exponentWordAt_of_memory he h.firstWindow,
    exponentWordAt_of_memory he h.parameterPointer,
    exponentWordAt_of_memory he h.firstWord,
    exponentWordAt_of_memory he h.inverse,
    exponentWordAt_of_memory he h.initialMask,
    exponentWordAt_of_memory he h.negativeInverse⟩
  apply Eq.trans _ h.initialWindow
  apply memLoad_congr
  intro i hi
  change (u.external[_]?).getD 0 = _
  rw [he]
  rfl

end P256.Proofs.Sec1.SquareRoot
