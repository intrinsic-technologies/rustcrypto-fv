import X86Proofs.Instructions.Movs.Execution
import P256.Proofs.Field.Inverse.State
import P256.Proofs.Field.Representation
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem nat256At_copy {s t : RamState} {src dst : BitVec 64} {x : Nat}
    (h : Nat256At s src x)
    (copy : ∀ i < 32, t.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]?) : Nat256At t dst x :=
  ⟨h.1, fun i hi => (copy i hi).trans (h.2 i hi)⟩

theorem nat256At_copy_limbs {s t : RamState} {src dst : BitVec 64} {x : Nat}
    (h : Nat256At s src x)
    (allocated : ∀ i < 32, (t.external[dst + BitVec.ofNat 64 i]?).isSome)
    (limbs : ∀ j < 4, memLoad t.external (dst + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (src + BitVec.ofNat 64 (8*j)) 64) : Nat256At t dst x :=
  nat256At_of_memLoad_limbs h.1 allocated (fun j hj => (limbs j hj).trans (h.memLoad_limb j hj))

theorem nat256At_zero_limbs {s : RamState} {addr : BitVec 64}
    (allocated : ∀ i < 32, (s.external[addr + BitVec.ofNat 64 i]?).isSome)
    (limbs : memLoad s.external (addr + 0) 64 = 0 ∧
      memLoad s.external (addr + 8) 64 = 0 ∧
      memLoad s.external (addr + 16) 64 = 0 ∧
      memLoad s.external (addr + 24) 64 = 0) : Nat256At s addr 0 := by
  apply nat256At_of_memLoad_limbs (by decide) allocated
  intro j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl
  · exact limbs.1
  · exact limbs.2.1
  · exact limbs.2.2.1
  · exact limbs.2.2.2

theorem stack_code_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len codeOffset codeLen : Nat}
    (hoff : offset ≤ 880) (hlen : len ≤ offset + 8)
    (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 880) (by simp) _
    (ScalarFrame.stack_contains pre hoff hlen ⟨i, hi, rfl⟩) (.inl ?_)
  rw [he, add_ofNat_add_ofNat]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

theorem memLoad32_lowByte (m : Ram) (address : BitVec 64) :
    (memLoad m address 32).setWidth 8 = (memByte m address).toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [memLoad, List.range_succ, hi]

end P256.Proofs.Field.Inverse
