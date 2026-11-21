import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Neg.SubLoad
import P256.Proofs.Common.Instructions.Sar.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines P256.Spec.Program P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] P256.Proofs.Common.Field.Instructions.subR64M64Effect

@[x86_local] theorem subR64M64Effect_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (P256.Proofs.Common.Field.Instructions.subR64M64Effect p dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro t t' h
    simp only [P256.Proofs.Common.Field.Instructions.subR64M64Effect, AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro t w hw
    simp only [P256.Proofs.Common.Field.Instructions.subR64M64Effect, List.mem_singleton] at hw
    subst w
    trivial

structure BorrowSlotPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (stackPtr s) 8
  avoids : ∀ a, (Component.mem (stackPtr s) 8).Covers a → ¬ InProgram a

theorem BorrowSlotPre.apart {p : BitVec 64} {s : RamState} (h : BorrowSlotPre p s)
    (offset len : Nat) (hc : offset + len ≤ 118431) :
    RangeApart (stackPtr s) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply h.avoids _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

theorem BorrowSlotPre.avoids_code {p : BitVec 64} {s : RamState} (h : BorrowSlotPre p s)
    (offset : Nat) (bytes : List UInt8) (hc : offset + bytes.length ≤ 118431)
    {e : Effect}
    (hm : ∀ c ∈ e.components, ∀ a len, c = .mem a len → a = stackPtr s ∧ len = 8) :
    e.Avoids (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) := by
  apply Effect.avoids_codeRange
  intro c hc' a len he
  obtain ⟨rfl, rfl⟩ := hm c hc' a len he
  exact h.apart offset bytes.length hc


end P256.Proofs.Field.Montgomery.Reduction
