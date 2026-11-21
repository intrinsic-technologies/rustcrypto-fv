import P256.Proofs.Program.Code
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize.Memory

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Instructions (bswap64)
open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def components (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip, .mem (s.regValue .rdi) 32]

theorem body_agrees {s loaded stored : RamState}
    (load : (loadEffect s).Holds s loaded)
    (store : (storeEffect loaded).Holds loaded stored) :
    AgreesExcept (components s) s stored := by
  have pointer : (Operand.reg 0 : Operand 64).read loaded = s.regValue .rdi :=
    load.writes.2.2.1
  have agrees : AgreesExcept
      ([.reg 1, .reg 2, .reg 0, .reg 7, .reg 6, .rip] ++
        [.mem (s.regValue .rdi) 8, .mem (s.regValue .rdi + 8) 8,
          .mem (s.regValue .rdi + 16) 8, .mem (s.regValue .rdi + 24) 8, .rip])
      s stored := by
    have h := load.agrees.trans store.agrees
    simpa only [loadEffect, storeEffect, Effect.components, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, Nat.reduceDiv,
      Write.component, Operand.component, pointer] using h
  apply agrees.widen
  · intro c hc hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl) <;> simp_all [components, Component.isMem]
  · intro a c hc hcover
    refine ⟨.mem (s.regValue .rdi) 32, by simp [components], ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl) <;> try exact hcover.elim
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨i, by omega, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨8 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨16 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨24 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩

theorem body_words {s loaded stored : RamState} {d : Nat}
    (scalar : Nat256At s (s.regValue .rsi) d)
    (load : (loadEffect s).Holds s loaded)
    (store : (storeEffect loaded).Holds loaded stored) :
    ∀ j < 4, (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*j)) :
      Operand 64).read stored = bswap64 (P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.canonicalLimb d (3-j)) := by
  have pointer : (Operand.reg 0 : Operand 64).read loaded = s.regValue .rdi :=
    load.writes.2.2.1
  have h0 := store.writes.1
  have h1 := store.writes.2.1
  have h2 := store.writes.2.2.1
  have h3 := store.writes.2.2.2
  change (Operand.mem ((Operand.reg 0 : Operand 64).read loaded) : Operand 64).read stored =
    (Operand.reg 1 : Operand 64).read loaded at h0
  change (Operand.mem ((Operand.reg 0 : Operand 64).read loaded + 8) : Operand 64).read stored =
    (Operand.reg 2 : Operand 64).read loaded at h1
  change (Operand.mem ((Operand.reg 0 : Operand 64).read loaded + 16) : Operand 64).read stored =
    (Operand.reg 7 : Operand 64).read loaded at h2
  change (Operand.mem ((Operand.reg 0 : Operand 64).read loaded + 24) : Operand 64).read stored =
    (Operand.reg 6 : Operand 64).read loaded at h3
  rw [pointer, load.writes.1] at h0
  rw [pointer, load.writes.2.1] at h1
  rw [pointer, load.writes.2.2.2.1] at h2
  rw [pointer, load.writes.2.2.2.2] at h3
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simpa only [P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.canonicalLimb, Nat.mul_zero, BitVec.reduceOfNat, BitVec.add_zero,
      Nat.reduceSub] using h0.trans (congrArg bswap64 (scalar.memLoad_limb 3 (by decide)))
  · simpa [P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.canonicalLimb] using
      h1.trans (congrArg bswap64 (scalar.memLoad_limb 2 (by decide)))
  · simpa [P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.canonicalLimb] using
      h2.trans (congrArg bswap64 (scalar.memLoad_limb 1 (by decide)))
  · have limb := scalar.memLoad_limb 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at limb
    simpa [P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.canonicalLimb] using
      h3.trans (congrArg bswap64 limb)

theorem body_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {d reserve : Nat}
    (pre : CalleePre s boundary 0x115960 32 32 reserve)
    (scalar : Nat256At s (s.regValue .rsi) d) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x11598d ∧
      AgreesExcept (components s) s t ∧
      Bytes t.external (s.regValue .rdi) 32 (fun i => UInt8.ofNat (d / 256^(31-i) % 256)) ∧
      t.regValue .rax = s.regValue .rdi := by
  obtain ⟨loadFuel, loaded, loadRun, loadReady, _, load⟩ :=
    load_correct boundary pre.outerBoundary s (readyToStep pre.machine pre.bindingsSupported)
      (programText_slice (programLoaded_codeIn pre.loaded) 0x15960 loadBytes
        (by decide +kernel) rfl) (load_pre pre)
  have memory : loaded.external = s.external := load.agrees.external (by
    simp [loadEffect, Effect.components, Component.Covers])
  have image : ProgramLoaded loaded := fun a b h => by rw [memory]; exact pre.loaded a b h
  obtain ⟨storeFuel, stored, storeRun, storeReady, _, store⟩ :=
    store_correct boundary pre.outerBoundary loaded loadReady
      (programText_slice (programLoaded_codeIn image) 0x1597e storeBytes
        (by decide +kernel) rfl) (store_pre pre load)
  have agrees := body_agrees load store
  refine ⟨loadFuel + storeFuel, stored, loadRun.trans storeRun, storeReady, store.rip,
    agrees, P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.canonical_bigEndian_bytes ?_ (body_words scalar load store), ?_⟩
  · intro i hi
    exact agrees.grow _ (Option.isSome_iff_exists.mpr
      (pre.outputAllocated _ (output_contains pre hi)))
  · exact (store.agrees.read (n := 64) (r := 0)
      (by simp [storeEffect, Effect.components])).trans load.writes.2.2.1

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize
