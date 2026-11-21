import P256.Proofs.Nonce.Initialize.Reduce.Interface
import P256.Proofs.Program.LimbSelect

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def selectionLayout : StackCallLayout 2144 32 32 80 :=
  ⟨288, 176, 272, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem selection_pre [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original difference : Nat} {select : Bool}
    (pre : InitializePre initial boundary orderAddress)
    (state : SelectionReady initial s boundary original difference select)
    (stage : Stage initial t boundary 288)
    (effect : (callEffect (fun _ => 0x1191c0) 0x107b5c s).Holds s t) :
    LimbSelect.Pre t boundary := by
  have dst : t.regValue .rdi = stackPtr initial - 272 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.destination
    change t.regValue .rdi = stackPtr s + 8 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have src : t.regValue .rdx = stackPtr initial - 176 := by
    have h := (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.source
    change t.regValue .rdx = stackPtr s + 104 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have ret : (returnBoundary t).rip = 0x107b5c := (callEffect_stack effect).1
  have cp := CalleePre.of_stack pre.toCalleePre selectionLayout stage.bindingsSupported
    stage.machine stage.directionFlag stage.loaded stage.allocated effect.rip stage.rsp
    src dst (ret ▸ inProgram_of_textOffset 0x7b5c (by decide))
  have lc : t.regValue .rsi = 4 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans state.leftCount
  refine {
    bindingsSupported := cp.bindingsSupported
    machine := cp.machine
    directionFlag := cp.directionFlag
    loaded := cp.loaded
    rip := cp.rip
    inputBounded := ?_
    inputAllocated := ?_
    outputBounded := cp.outputBounded
    outputAllocated := cp.outputAllocated
    stack := cp.stack
    separation := ?_
    avoids := cp.avoids
    outerBoundary := cp.outerBoundary
    returnInProgram := cp.returnInProgram
    leftCount := lc
    rightCount := (effect.agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])).trans state.rightCount
    sourceBounded := cp.inputBounded
    sourceAllocated := cp.inputAllocated
    sourceOutput := cp.separation 0 1 (by decide)
    sourceStack := cp.separation 0 2 (by decide)
  }
  · change (t.regValue .rsi).toNat + 0 < 2^32
    rw [lc]
    decide
  · intro a ha
    have low := ha.1
    have high := ha.2
    change (t.regValue .rsi).toNat ≤ a.toNat at low
    change a.toNat < (t.regValue .rsi).toNat + 0 at high
    omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 0 at ha
      omega
    · intro a ha
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 0 at ha
      omega
    · exact cp.separation 1 2 (by decide)

end P256.Proofs.Nonce.Initialize.Reduce
