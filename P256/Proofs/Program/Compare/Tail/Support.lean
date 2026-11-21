import P256.Proofs.Program.Compare.Tail.Gate
import P256.Proofs.Program.Compare.Tail.ByteGate

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def changes : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .flags, .rip]

structure PhaseSuccess (s t : RamState) (count : Nat) (next : BitVec 64) : Prop where
  rip : t.RIP = next
  length : (Operand.reg 1 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s
  left : (Operand.reg 6 : Operand 64).read t =
    (Operand.reg 6 : Operand 64).read s + BitVec.ofNat 64 count
  right : (Operand.reg 2 : Operand 64).read t =
    (Operand.reg 2 : Operand 64).read s + BitVec.ofNat 64 count
  equal : BytesEqual s ((Operand.reg 6 : Operand 64).read s)
    ((Operand.reg 2 : Operand 64).read s) count

def PhaseFailure (s t : RamState) (count : Nat) : Prop :=
  t.RIP = 0x11ce9e ∧ (Operand.reg 0 : Operand 32).read t ≠ 0 ∧
    ¬ BytesEqual s ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s) count

theorem phaseSuccess_slice {s t : RamState} {count rest : Nat} {next : BitVec 64}
    (hp : PhaseSuccess s t count next) (hm : t.external = s.external) :
    BytesEqual t ((Operand.reg 6 : Operand 64).read t)
        ((Operand.reg 2 : Operand 64).read t) rest ↔
      BytesEqual s ((Operand.reg 6 : Operand 64).read s)
        ((Operand.reg 2 : Operand 64).read s) (count + rest) := by
  rw [bytesEqual_append]
  simp only [hp.left, hp.right, BytesEqual, hm]
  exact ⟨fun h ↦ ⟨hp.equal, h⟩, And.right⟩

theorem branch_zero [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (p : BitVec 64) (disp : BitVec 8)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programSections.toCodeMap s)
    (hBoundary : RegisterBoundary boundary s) (hRip : s.RIP = p)
    (hBytes : CodeIn (codeRange p (jccOpcode8 5 :: immBytes 8 disp)) s)
    (hNext : InRoutine (p + 2))
    (hTarget : InRoutine (branchTarget p 2 (disp.signExtend 64)))
    (hZero : (StatusFlags.ofRFLAGS s.RFLAGS).ZF = true) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ stackPtr t = stackPtr s ∧
      AgreesExcept [.rip] s t ∧ t.RIP = p + (2 : BitVec 64) := by
  obtain ⟨fuel, t, ha, ht, _, he, hsp⟩ :=
    branch8 p 5 disp hNext hTarget boundary s hReady hBytes hRip hBoundary
  refine ⟨fuel, t, ha, ht, he.codeIn (branchEffect_avoids _ _ _ _) hCode, hsp,
    he.agrees, ?_⟩
  simpa [jccEffect, branchEffect, condHolds, hZero] using he.rip

end P256.Proofs.Program.Compare.Tail
