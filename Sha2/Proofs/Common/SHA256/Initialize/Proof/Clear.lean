import Sha2.Proofs.Common.SHA256.Initialize.Proof.WordStore
import Sha2.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

theorem Clear.run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (b : Clear)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p b.bytes.length) :
    b.Contract boundary p := by
  intro s ready code pre
  let n := 7 + b.counter.mode.tail.length
  let m := 3 + b.tail.mode.tail.length
  have firstLength : (encodeMovM64Imm32 b.counter.mode 0).length = n := by
    simp [encodeMovM64Imm32, immBytes_length, n]; omega
  have lastLength : ([0xc6, b.tail.mode.modrm 0] ++ b.tail.mode.tail ++ [0]).length = m := by
    simp [m]; omega
  have bytes : b.bytes = encodeMovM64Imm32 b.counter.mode 0 ++
      ([0xc6, b.tail.mode.modrm 0] ++ b.tail.mode.tail ++ [0]) := by
    simp only [Clear.bytes, List.append_assoc]
  have len : b.bytes.length = n + m := by rw [bytes, List.length_append, firstLength, lastLength]
  have firstCode : CodeIn (codeRange p (encodeMovM64Imm32 b.counter.mode 0)) s := by
    apply code.mono
    rw [bytes, codeRange_append]
    exact fun _ h => List.mem_append_left _ h
  obtain ⟨u, first, readyU, counter⟩ := (counter_step p b.counter pre.counterValid).advances
    (boundary := boundary) ready firstCode
    ⟨pre.rip, pre.counterWritable, by simpa only [BitVec.add_zero] using RangeApart.sub pre.counterApart 0 n (by rw [len]; omega)⟩
    (boundary_ne_program outside (inside n (by rw [len]; omega)))
  have address (a : Address) : a.read u = a.read s := by
    apply Address.read_eq
    exact counter.agrees.read (by simp [movM64Imm32Effect, storeEffect,
      Effect.components, Write.component, Operand.component])
  have codeU : CodeIn (codeRange p b.bytes) u := counter.codeIn (by
    apply Effect.avoids_codeRange
    simpa [movM64Imm32Effect, storeEffect, Effect.components, Write.component,
      Operand.component, storeAddrAt, Address.mode_addr] using pre.counterApart) code
  have secondCode : CodeIn (codeRange (p + BitVec.ofNat 64 n)
      ([0xc6, b.tail.mode.modrm 0] ++ b.tail.mode.tail ++ [0])) u := by
    apply codeU.mono
    rw [bytes, codeRange_append p (encodeMovM64Imm32 b.counter.mode 0), firstLength]
    exact fun _ h => List.mem_append_right _ h
  obtain ⟨t, second, readyT, tail⟩ :=
    (tail_step (p + BitVec.ofNat 64 n) b.tail pre.tailValid pre.tailRexX pre.tailRexB).advances
      (boundary := boundary) readyU secondCode
      ⟨counter.rip, by rw [address]; exact pre.tailWritable.of_holds counter,
        by rw [address]; exact RangeApart.sub pre.tailApart n m (by rw [len]; exact Nat.le_refl _)⟩
      (by
        change p + BitVec.ofNat 64 n + BitVec.ofNat 64 m ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← len]
        exact boundary_ne_program outside (inside _ (Nat.le_refl _)))
  have codeT : CodeIn (codeRange p b.bytes) t := tail.codeIn (by
    apply Effect.avoids_codeRange
    simpa [movM8Imm8Effect, storeEffect, Effect.components, Write.component,
      Operand.component, storeAddrAt, Address.mode_addr, address] using pre.tailApart) codeU
  refine ⟨2, t, first.trans second, readyT, codeT, ?_, ?_, trivial, ?_⟩
  · simpa only [Clear.effect, movM8Imm8Effect, storeEffect, len,
      m, BitVec.ofNat_add, BitVec.add_assoc] using tail.rip
  · change memLoad t.external (b.counter.read s) 64 = 0 ∧
      memLoad t.external (b.tail.read s) 8 = 0
    constructor
    · have unchanged := Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees
        (n := 64) tail.agrees (b.counter.read s) (by
          intro i hi c hc
          simp [movM8Imm8Effect, storeEffect, Effect.components, Write.component,
            Operand.component, storeAddrAt, Address.mode_addr, address] at hc
          rcases hc with rfl | rfl
          · exact fun ⟨j, hj, heq⟩ => pre.separate i hi j hj heq
          · simp [Component.Covers])
      exact unchanged.trans (by simpa [movM64Imm32Effect, storeEffect,
        storeAddrAt, Address.mode_addr, Write.AllHold, Operand.read] using counter.writes)
    · simpa [movM8Imm8Effect, storeEffect, storeAddrAt, Address.mode_addr, address, Write.AllHold, Operand.read]
        using tail.writes
  · apply (counter.agrees.trans tail.agrees).mono
    intro c hc
    simp only [movM64Imm32Effect, movM8Imm8Effect, storeEffect, Clear.effect,
      Effect.components, storeAddrAt,
      Address.mode_addr, address] at hc ⊢
    simp at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl <;> simp

end Sha2.Proofs.Common.SHA256.Initialize
