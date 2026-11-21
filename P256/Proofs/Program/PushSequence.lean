import P256.Proofs.Program.Push
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def pushSequenceSize : List (BitVec 4) → Nat
  | [] => 0
  | source :: rest => (encodePushR64 source).length + pushSequenceSize rest

def PushSequenceCode (offset : Nat) : List (BitVec 4) → Prop
  | [] => True
  | source :: rest =>
    offset + (encodePushR64 source).length < 118431 ∧
    Extracted.textBytes.toListFrom offset (encodePushR64 source).length = encodePushR64 source ∧
    PushSequenceCode (offset + (encodePushR64 source).length) rest

def pushSequenceMemory (s : RamState) (memory : Ram) (offset : Nat) : List (BitVec 4) → Ram
  | [] => memory
  | source :: rest =>
    pushSequenceMemory s
      (memStore memory (stackPtr s - BitVec.ofNat 64 (offset + 8))
        ((Operand.reg (source.setWidth 5) : Operand 64).read s)) (offset + 8) rest

def pushSequenceFrame (s : RamState) (offset : Nat) : List (BitVec 4) → List Component
  | [] => []
  | _ :: rest => [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 (offset + 8)) 8, .rip] ++
      pushSequenceFrame s (offset + 8) rest

theorem push_sequence [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {reserve offset codeOffset : Nat} (sources : List (BitVec 4))
    (stack : Stack.Valid s reserve)
    (avoids : (Stack.region s reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grown : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 offset)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (capacity : offset + 8 * sources.length ≤ reserve) (aligned : offset % 8 = 0)
    (safe : ∀ source ∈ sources, source.setWidth 5 ≠ (4 : BitVec 5))
    (values : ∀ source ∈ sources,
      (Operand.reg (source.setWidth 5) : Operand 64).read t =
        (Operand.reg (source.setWidth 5) : Operand 64).read s)
    (code : PushSequenceCode codeOffset sources) :
    ∃ u, Advances boundary sources.length t u ∧ ReadyToStep u ∧ ProgramLoaded u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + pushSequenceSize sources) ∧
      stackPtr u = stackPtr s - BitVec.ofNat 64 (offset + 8 * sources.length) ∧
      u.external = pushSequenceMemory s t.external offset sources ∧
      AgreesExcept (pushSequenceFrame s offset sources) t u := by
  induction sources generalizing t offset codeOffset with
  | nil =>
    refine ⟨t, ?_, ready, loaded, ?_, ?_, rfl, ?_⟩
    · rfl
    · simpa only [pushSequenceSize, Nat.add_zero] using rip
    · simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using rsp
    · exact AgreesExcept.refl _ _
  | cons source rest ih =>
    obtain ⟨v, run, readyV, loadedV, ripV, rspV, agrees, memory⟩ :=
      push_exists stack avoids outside ready loaded grown source offset codeOffset rsp rip
        (by simp only [List.length_cons] at capacity; omega) (by omega) code.1 code.2.1
    have valuesV : ∀ r ∈ rest, (Operand.reg (r.setWidth 5) : Operand 64).read v =
        (Operand.reg (r.setWidth 5) : Operand 64).read s := by
      intro r hr
      apply (agrees.read (n := 64) (r := r.setWidth 5) ?_).trans
        (values r (by simp [hr]))
      simp
      exact safe r (by simp [hr])
    obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
      ih readyV loadedV (fun a ha => agrees.grow a (grown a ha)) rspV ripV
        (by simp only [List.length_cons] at capacity; omega) (by omega)
        (fun r hr => safe r (by simp [hr])) valuesV code.2.2
    refine ⟨u, ?_, readyU, loadedU, ?_, ?_, ?_, agrees.trans agreesU⟩
    · simpa only [List.length_cons, Nat.add_comm 1] using run.trans runU
    · simpa only [pushSequenceSize, Nat.add_assoc] using ripU
    · have sum : offset + 8 * (source :: rest).length = offset + 8 + 8 * rest.length := by
        simp only [List.length_cons]
        omega
      rw [sum]
      exact rspU
    · rw [memoryU, memory, values source (by simp)]
      rfl

end P256.Proofs.Program
