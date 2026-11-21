import P256.Proofs.Signing.Core.Initialize.CallState
import P256.Proofs.Signing.Core.Initialize.Memory
import P256.Proofs.Program.CalleeStackRegion
import P256.Proofs.Nonce.Initialize.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)
open SecretKeyFromBytes.Scalar (Nat256At)

def nonceLayout : StackCallLayout 4584 32 72 2144 :=
  ⟨2304, 1752, 120, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem nonce_pre [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {secret : Nat}
    (pre : SignPre s boundary) (input : CallInput s t secret) (entered : Entered s t u) :
    Nonce.InitializePre u boundary (frameBase s + 272) := by
  have si : u.regValue .rsi = frameBase s + 528 :=
    (entered.registers .rsi (by decide)).trans input.rsi
  have di : u.regValue .rdi = frameBase s + 2160 :=
    (entered.registers .rdi (by decide)).trans input.rdi
  have cx : u.regValue .rcx = s.regValue .rdx :=
    (entered.registers .rcx (by decide)).trans input.rcx
  have src : u.regValue .rsi = stackPtr s - 1752 := si.trans (base_add s (by decide))
  have dst : u.regValue .rdi = stackPtr s - 120 := di.trans (base_add s (by decide))
  have cp := CalleePre.of_stack pre.toCalleePre nonceLayout entered.frame.bindingsSupported
    entered.frame.machine entered.frame.directionFlag entered.frame.loaded entered.frame.allocated
    entered.rip entered.frame.rsp src dst
    (entered.returnAddress ▸ inProgram_of_textOffset 0xca6f (by decide))
  have sub := nonceLayout.regions_within pre.stack entered.frame.rsp src dst
  have outSub (a : Nat) (ha : (registerRegion u .rdi 72).Contains a) :
      (Stack.region s 4584).Contains a := sub _ (by simp) _ ha
  have stackSub (a : Nat) (ha : (Stack.region u 2144).Contains a) :
      (Stack.region s 4584).Contains a := sub _ (by simp) _ ha
  have bounds := stack_bounds pre.stack
  have ord : (frameBase s + 272).toNat = (stackPtr s).toNat - 2280 + 272 := base_nat pre (by decide)
  have din : (u.regValue .rdi).toNat = (stackPtr s).toNat - 2280 + 2160 := by
    rw [di]; exact base_nat pre (by decide)
  have sp : (stackPtr u).toNat = (stackPtr s).toNat - 2304 := by
    rw [entered.frame.rsp]; exact stack_sub_toNat pre.stack (by decide)
  have arg : (u.regValue .rsp + 8).toNat = (stackPtr s).toNat - 2296 := by
    change (stackPtr u + 8).toNat = _
    rw [BitVec.toNat_add, sp]
    simp only [BitVec.reduceToNat]
    omega
  have alloc (region : MemoryRegion)
      (lo : (stackPtr s).toNat - 4584 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      region.Allocated u.external := by
    intro a ha
    apply Option.isSome_iff_exists.mp (entered.frame.allocated a ?_)
    apply Option.isSome_iff_exists.mpr (pre.stack.2.1 a ?_)
    change region.start ≤ a.toNat ∧ a.toNat < region.start + region.size at ha
    change (stackPtr s).toNat - 4584 ≤ a.toNat ∧ a.toNat < (Stack.region s 4584).start + (Stack.region s 4584).size
    rw [stack_region_end]
    omega
  have cxRegion : registerRegion u .rcx 32 = registerRegion s .rdx 32 := by simp only [registerRegion, cx]
  refine ⟨cp, (entered.registers .rdx (by decide)).trans input.rdx,
    (entered.registers .r8 (by decide)).trans input.r8,
    (entered.registers .r9 (by decide)).trans input.r9,
    cxRegion ▸ pre.digestBounded, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    entered.entropyLength, entered.orderPointer, ?_⟩
  · rw [cxRegion]
    intro a ha
    exact Option.isSome_iff_exists.mp (entered.frame.allocated a
      (Option.isSome_iff_exists.mpr (pre.digestAllocated a ha)))
  · rw [cxRegion]
    intro a hi ho
    exact pre.digestStack a hi (outSub a ho)
  · rw [cxRegion]
    intro a hi hs
    exact pre.digestStack a hi (stackSub a hs)
  · change (frameBase s + 272).toNat + 32 < 2^32
    rw [ord]; omega
  · exact alloc _ (by dsimp only; rw [ord]; omega) (by dsimp only; rw [ord]; omega)
  · intro a hi ho
    change (frameBase s + 272).toNat ≤ a ∧ a < (frameBase s + 272).toNat + 32 at hi
    change (u.regValue .rdi).toNat ≤ a ∧ a < (u.regValue .rdi).toNat + 72 at ho
    rw [ord] at hi; rw [din] at ho; omega
  · intro a hi hs
    change (frameBase s + 272).toNat ≤ a ∧ a < (frameBase s + 272).toNat + 32 at hi
    have high := hs.2
    rw [stack_region_end] at high
    change a < (stackPtr u).toNat + 8 at high
    rw [ord] at hi; rw [sp] at high; omega
  · change (u.regValue .rsp + 8).toNat + 16 < 2^32
    rw [arg]; omega
  · exact alloc _ (by dsimp only; rw [arg]; omega) (by dsimp only; rw [arg]; omega)
  · intro a hi ho
    change (u.regValue .rsp + 8).toNat ≤ a ∧ a < (u.regValue .rsp + 8).toNat + 16 at hi
    change (u.regValue .rdi).toNat ≤ a ∧ a < (u.regValue .rdi).toNat + 72 at ho
    rw [arg] at hi; rw [din] at ho; omega
  · refine ⟨input.order.1, fun i hi => ?_⟩
    have copied := entered.bytes (272+i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at copied
    exact copied.trans (input.order.2 i hi)

end P256.Proofs.Signing.Core.Initialize
