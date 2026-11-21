import Sha2.Proofs.Common.SHA256.Initialize.Proof.Encoding

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

theorem register_ne {a b : BitVec 4} (h : a ≠ b) : a.setWidth 5 ≠ b.setWidth 5 := by
  intro equal
  apply h
  have narrow := congrArg (fun x : BitVec 5 => x.setWidth 4) equal
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 4 ≤ 5), BitVec.setWidth_eq] using narrow

theorem WordStore.run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (b : WordStore v)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p b.bytes.length) :
    b.Contract boundary p := by
  intro s ready code pre
  have storeLength : (encodeMovM64R64 b.register b.destination.mode).length =
      3 + b.destination.mode.tail.length := by simp [encodeMovM64R64]; omega
  cases loading : b.loadConstant with
  | false =>
    have bytes : b.bytes = encodeMovM64R64 b.register b.destination.mode := by
      simp only [WordStore.bytes, loading, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    have len : b.bytes.length = 3 + b.destination.mode.tail.length := bytes ▸ storeLength
    obtain ⟨t, run, readyT, result⟩ := (word_step p b.register b.destination pre.valid).advances (boundary := boundary)
      ready (bytes ▸ code) ⟨pre.rip, pre.writable, len ▸ pre.apart⟩
      (by change p + BitVec.ofNat 64 (3 + b.destination.mode.tail.length) ≠ boundary.rip; rw [← len]; exact boundary_ne_program outside (inside _ (Nat.le_refl _)))
    have avoids : (movM64R64Effect p (b.register.setWidth 5) b.destination.mode s).Avoids
        (codeRange p b.bytes) := by
      apply Effect.avoids_codeRange
      simpa [movM64R64Effect, storeEffect, Effect.components, Write.component,
        Operand.component, storeAddrAt, Address.mode_addr] using pre.apart
    refine ⟨1, t, run, readyT, result.codeIn avoids code, ?_⟩
    simpa only [Effect.post, WordStore.effect, loading, Bool.false_eq_true, ↓reduceIte, List.nil_append,
      movM64R64Effect, storeEffect, Address.storeAddrAt, storeAddrAt, Address.mode_addr, len, pre.value loading] using result
  | true =>
    have bytes : b.bytes = encodeMovR64Imm64 b.register (packedWord b.index v) ++
        encodeMovM64R64 b.register b.destination.mode := by simp only [WordStore.bytes, loading, ↓reduceIte]
    have loadLength : (encodeMovR64Imm64 b.register (packedWord b.index v)).length = 10 := by
      simp only [encodeMovR64Imm64, List.length_cons, immBytes_length]
    have len : b.bytes.length = 10 + (3 + b.destination.mode.tail.length) := by
      rw [bytes, List.length_append, loadLength, storeLength]
    have firstCode : CodeIn (codeRange p (encodeMovR64Imm64 b.register (packedWord b.index v))) s := by
      apply code.mono
      rw [bytes, codeRange_append]
      exact fun _ h => List.mem_append_left _ h
    obtain ⟨u, first, readyU, loaded⟩ := (immediate_step p b.register (packedWord b.index v)).advances (boundary := boundary)
      ready firstCode pre.rip
      (boundary_ne_program outside (inside 10 (by rw [len]; omega)))
    have codeU : CodeIn (codeRange p b.bytes) u := loaded.codeIn
      (Effect.Avoids.of_noMem (by simp [movR64Imm64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]) _) code
    have address : b.destination.read u = b.destination.read s := by
      apply Address.read_eq
      apply loaded.agrees.read
      simpa [movR64Imm64Effect, Effect.components, Write.component, Operand.component]
        using register_ne (Ne.symm (pre.independent loading))
    have secondCode : CodeIn
        (codeRange (p + 10) (encodeMovM64R64 b.register b.destination.mode)) u := by
      apply codeU.mono
      rw [bytes, codeRange_append, loadLength]
      exact fun _ h => List.mem_append_right _ h
    obtain ⟨t, second, readyT, stored⟩ :=
      (word_step (p + 10) b.register b.destination pre.valid).advances (boundary := boundary) readyU secondCode
        ⟨loaded.rip, by rw [address]; exact pre.writable.of_holds loaded,
          by rw [address]; exact RangeApart.sub pre.apart 10 _ (by rw [len]; exact Nat.le_refl _)⟩
        (by
          change p + 10 + BitVec.ofNat 64 (3 + b.destination.mode.tail.length) ≠ boundary.rip
          rw [show (10 : BitVec 64) = BitVec.ofNat 64 10 from rfl,
            BitVec.add_assoc, ← BitVec.ofNat_add]
          exact boundary_ne_program outside (inside _ (by rw [len]; exact Nat.le_refl _)))
    have avoids : (movM64R64Effect (p + 10) (b.register.setWidth 5) b.destination.mode u).Avoids
        (codeRange p b.bytes) := by
      apply Effect.avoids_codeRange
      simpa [movM64R64Effect, storeEffect, Effect.components, Write.component,
        Operand.component, storeAddrAt, Address.mode_addr, address] using pre.apart
    refine ⟨2, t, first.trans second, readyT, stored.codeIn avoids codeU, ?_⟩
    refine ⟨?_, ?_, trivial, ?_⟩
    · simpa only [WordStore.effect, movM64R64Effect, storeEffect, len, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat] using stored.rip
    · simp only [WordStore.effect, loading, ↓reduceIte, List.singleton_append] 
      change ((.reg (b.register.setWidth 5) : Operand 64).read t = packedWord b.index v) ∧
        memLoad t.external (b.destination.read s) 64 = packedWord b.index v
      constructor
      · exact (stored.agrees.read (by simp [movM64R64Effect, Effect.components,
          storeEffect, Write.component, Operand.component])).trans loaded.writes
      · have word := stored.writes
        change memLoad t.external (b.destination.mode.addr u _) 64 = _ at word
        rw [Address.mode_addr, address] at word
        exact word.trans loaded.writes
    · apply (loaded.agrees.trans stored.agrees).mono
      intro c member
      simp only [movR64Imm64Effect, movM64R64Effect, storeEffect, WordStore.effect,
        loading, ↓reduceIte, Effect.components, List.map_cons, List.map_nil,
        List.map_append, List.mem_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false, storeAddrAt, Address.mode_addr, address] at member ⊢
      rcases member with (rfl | rfl) | rfl | rfl <;> simp

end Sha2.Proofs.Common.SHA256.Initialize
