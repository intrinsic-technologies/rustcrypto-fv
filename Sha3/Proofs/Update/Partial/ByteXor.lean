import Sha3.Proofs.Finalize.Padding.Bytes
import Sha3.Proofs.Stores.ByteXor
import Sha3.Proofs.X86.Instructions.MovzxLoad.Triple
import Sha3.Proofs.Run

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha3.Proofs.Finalize.Padding

theorem xor_prefix_byte {m : Ram} {base : BitVec 64} {len count : Nat}
    {initial input : Nat → UInt8}
    (h : Bytes m base len (fun i ↦ initial i ^^^ (if i < count then input i else 0)))
    (hlen : len ≤ 2 ^ 64) (hcount : count < len) :
    Bytes (memStore m (base + BitVec.ofNat 64 count)
      (memLoad m (base + BitVec.ofNat 64 count) 8 ^^^ (input count).toBitVec)) base len
      (fun i ↦ initial i ^^^ (if i < count + 1 then input i else 0)) := by
  rw [h.loadByte count hcount]
  simp only [Nat.lt_irrefl, ↓reduceIte, UInt8.xor_zero]
  change Bytes (memStore m (base + BitVec.ofNat 64 count)
    ((initial count ^^^ input count).toBitVec)) base len _
  apply (h.writeByte hlen count hcount (initial count ^^^ input count)).congr
  intro i _
  by_cases hi : i = count
  · subst i
    simp only [↓reduceIte, Nat.lt_add_one]
  · have hlt : i < count + 1 ↔ i < count := by omega
    simp only [hi, ↓reduceIte, hlt]

theorem xor_prefix_four {m : Ram} {base : BitVec 64} {len count : Nat}
    {initial input : Nat → UInt8}
    (h : Bytes m base len (fun i ↦ initial i ^^^ (if i < count then input i else 0)))
    (hlen : len ≤ 2 ^ 64) (hcount : count + 4 ≤ len) :
    let step := fun m i ↦ memStore m (base + BitVec.ofNat 64 i)
      (memLoad m (base + BitVec.ofNat 64 i) 8 ^^^ (input i).toBitVec)
    Bytes (step (step (step (step m count) (count + 1)) (count + 2)) (count + 3)) base len
      (fun i ↦ initial i ^^^ (if i < count + 4 then input i else 0)) := by
  dsimp only
  exact xor_prefix_byte (xor_prefix_byte (xor_prefix_byte
    (xor_prefix_byte h hlen (by omega)) hlen (by omega)) hlen (by omega)) hlen (by omega)

section BytePair

variable [Bindings] (boundary : ReturnBoundary) (code loadCode storeCode : CodeMap)
    (p : BitVec 64) (loadLen storeLen : Nat) (reg : BitVec 5) (loadMode storeMode : AddrMode)
    (hload : StepEffect
      (LoadPre p (fun s ↦ loadMode.addr s (p + BitVec.ofNat 64 loadLen)) 1) loadCode
      (movzxR32M8Effect p loadLen reg loadMode))
    (hstore : StepEffect
      (StorePreReadable (p + BitVec.ofNat 64 loadLen)
        (storeAddrAt (p + BitVec.ofNat 64 loadLen) storeMode storeLen) 1) storeCode
      (xorMREffect (p + BitVec.ofNat 64 loadLen) storeLen 8 reg storeMode))
    (hloadCode : ∀ byte ∈ loadCode, byte ∈ code)
    (hstoreCode : ∀ byte ∈ storeCode, byte ∈ code)
    (hne₁ : p + BitVec.ofNat 64 loadLen ≠ boundary.rip)
    (hne₂ : p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen ≠ boundary.rip)

include hload hstore hloadCode hstoreCode hne₁ hne₂ in
 theorem load_xor_byte (s : RamState) (hready : ReadyToStep s) (hcode : CodeIn code s)
    (hip : s.RIP = p)
    (hsource : MemReadable s (loadMode.addr s (p + BitVec.ofNat 64 loadLen)) 1)
    (hdest : MemReadable s
      (storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen)) 1)
    (hstable : ∀ u, AgreesExcept [.reg reg, .rip] s u →
      storeMode.addr u (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen) =
      storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen))
    (htables : ¬ Spec.Program.InPageTables
      (storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen)))
    (hseparate : ∀ byte ∈ code, byte.1 ≠
      storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen)) :
    ∃ t : RamState, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = BitVec.add (p + BitVec.ofNat 64 loadLen) (BitVec.ofNat 64 storeLen) ∧
      t.external = memStore s.external
        (storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen))
        (memLoad s.external
            (storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen)) 8 ^^^
          memLoad s.external (loadMode.addr s (p + BitVec.ofNat 64 loadLen)) 8) ∧
      AgreesExcept [.reg reg,
        .mem (storeMode.addr s (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen)) 1,
        .flags, .rip] s t := by
  obtain ⟨u, hrun₁, hready₁, hu⟩ :=
    hload.advances hready (hcode.mono hloadCode) ⟨hip, hsource⟩ hne₁
  have hext : u.external = s.external :=
    hu.agrees.external (by simp [movzxR32M8Effect_components, Component.Covers])
  have hc₁ : CodeIn code u := hu.codeIn
    (Effect.Avoids.of_noMem (by simp [movzxR32M8Effect_components, Component.Covers]) code) hcode
  have hdst := hstable u hu.agrees
  have hsrc : (Operand.reg reg : Operand 8).read u =
      memLoad s.external (loadMode.addr s (p + BitVec.ofNat 64 loadLen)) 8 := by
    have hv := hu.writes
    change (Operand.reg reg : Operand 64).read u =
      (memLoad s.external (loadMode.addr s (p + BitVec.ofNat 64 loadLen)) 8).setWidth 64 at hv
    change ((Operand.reg reg : Operand 64).read u).setWidth 8 = _
    rw [hv]
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  have hstorePre : StorePreReadable (p + BitVec.ofNat 64 loadLen)
      (storeAddrAt (p + BitVec.ofNat 64 loadLen) storeMode storeLen) 1 u := by
    refine ⟨⟨hu.rip, ?_⟩, ?_⟩
    · simpa only [storeAddrAt, hdst] using hdest.of_external_eq hext
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simpa only [storeAddrAt, hdst, BitVec.add_zero] using htables
  obtain ⟨t, hrun₂, hready₂, ht⟩ := hstore.advances hready₁ (hc₁.mono hstoreCode) hstorePre hne₂
  have hmemory := single_store_external (by decide) hstorePre.1.read.mem ht
  change t.external = memStore u.external
    (storeMode.addr u (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen))
    (memLoad u.external
        (storeMode.addr u (p + BitVec.ofNat 64 loadLen + BitVec.ofNat 64 storeLen)) 8 ^^^
      (Operand.reg reg : Operand 8).read u) at hmemory
  rw [hdst, hsrc, hext] at hmemory
  refine ⟨t, hrun₁.trans hrun₂, hready₂, ?_, ht.rip, hmemory, ?_⟩
  · apply ht.codeIn ?_ hc₁
    intro byte hb c hc hcov
    simp only [xorMREffect_components, hdst, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨i, hi, hiaddr⟩ := hcov
      have hi0 : i = 0 := by omega
      apply hseparate byte hb
      simpa only [hi0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hiaddr
    · exact hcov
    · exact hcov
  · apply (hu.agrees.trans ht.agrees).mono
    simp only [movzxR32M8Effect_components, xorMREffect_components, hdst]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (rfl | rfl) | rfl | rfl | rfl <;> simp

end BytePair


end Sha3.Proofs.Update.Partial
