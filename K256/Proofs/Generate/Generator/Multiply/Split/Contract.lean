import K256.Proofs.Generate.Generator.Multiply.Split.Prologue
import K256.Proofs.Generate.LIR.Fn11b8f0.Frame
import K256.Proofs.Generate.LIR.Fn1099c0.Frame
import K256.Proofs.Generate.LIR.Fn1109b0.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

def ScalarRoutine (entry : Label) (layout : Label → Activation → List Atom)
    (doneAt : Activation → List Atom) (window : Nat) (usesOrder : Bool)
    (result : Nat → Nat → Nat) : Prop :=
  ∀ {fr : Activation} {a : Registers} {m : Ram} {x y : Nat},
    Atom.All Extracted.programImage a m (layout entry fr) →
    (∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) →
    (usesOrder = true → fr.rcx = 0x2021a0) →
    x < domain.n → y < domain.n →
    Readable m fr.rsi 32 → Readable m fr.rdx 32 → Writable Extracted.programImage m fr.rdi 32 →
    fr.rsp.toNat + 8 ≤ fr.rdi.toNat →
    (∀ src ∈ [fr.rsi, fr.rdx],
      (src.toNat + 32 ≤ fr.rsp.toNat - window ∨ fr.rsp.toNat + 8 ≤ src.toNat) ∧
      (src.toNat + 32 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ src.toNat)) →
    WordsAt m fr.rsi 64 (scalarWords x) → WordsAt m fr.rdx 64 (scalarWords y) →
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨entry, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ WordsAt out.store fr.rdi 64 (scalarWords (result x y)) ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - window, window⟩, ⟨fr.rdi.toNat, 32⟩]

abbrev AddExecution := ScalarRoutine .l1109b0 Fn1109b0.frameAt Fn1109b0.doneAt 0x40 true
  (fun x y => (x + y) % domain.n)

abbrev MulExecution := ScalarRoutine .l1099c0 Fn1099c0.frameAt Fn1099c0.doneAt 0x141 false
  (fun x y => (x * y) % domain.n)

abbrev RoundExecution := ScalarRoutine .l11b8f0 Fn11b8f0.frameAt Fn11b8f0.doneAt 0xe0 false
  Generate.Curve.mulShift384

end K256.Proofs.Generate.Generator.Multiply.Split
