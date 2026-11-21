import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Image
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Decoding

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

theorem decode_advanceNoMemReady [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} {entry : BitVec 64} {offset : Nat}
    {bytes : List UInt8} {e : RamState → Effect}
    (hentry : EntryReady programImage s)
    (hstep : StepEffect (fun u => u.RIP = entry + BitVec.ofNat 64 offset)
      (codeRange (entry + BitVec.ofNat 64 offset) bytes) e)
    (hsub : ∀ x ∈ codeRange (entry + BitVec.ofNat 64 offset) bytes, x ∈ programImage)
    (hp : s.RIP = entry + BitVec.ofNat 64 offset) (hret : ¬ InProgram boundary.rip)
    (hnext : InProgram (e s).rip) (havoid : (e s).Avoids programImage) :
    ∃ t, Advances boundary 1 s t ∧ EntryReady programImage t ∧ (e s).Holds s t := by
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset entry offset hstep hentry.ready hentry.code hsub hp hret hnext havoid
  exact ⟨t, ha, Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hentry hr hc he.agrees, he⟩

theorem decode_codeRangeInImage {entry : BitVec 64} {offset : Nat}
    {bytes : List UInt8}
    (h : ∀ i : Fin bytes.length,
      (entry + BitVec.ofNat 64 offset + BitVec.ofNat 64 i.val, bytes[i]) ∈ programImage) :
    ∀ x ∈ codeRange (entry + BitVec.ofNat 64 offset) bytes, x ∈ programImage := by
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact h i

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
