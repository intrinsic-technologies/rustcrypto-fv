import Sha1.Proofs.Common.Instructions.StorePre

namespace Sha1.Proofs.Common

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec.Program

structure StoreRegion (code : CodeMap) (mem : Ram) (region : MemoryRegion) : Prop where
  bounded : region.Bounded
  allocated : region.Allocated mem
  avoids : region.Avoids fun address ↦ (∃ byte, (address, byte) ∈ code) ∨ InPageTables address

structure OutputFrameContract (code : CodeMap) (mem : Ram)
    (output stack : MemoryRegion) : Prop where
  output : StoreRegion code mem output
  stack : StoreRegion code mem stack

theorem StoreRegion.contains_byte {region : MemoryRegion} {addr : BitVec 64} {len i : Nat}
    (hin : InRegion region addr len) (hi : i < len) :
    region.Contains (addr + BitVec.ofNat 64 i).toNat := by
  obtain ⟨hstart, hend, h64⟩ := hin
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, by omega⟩

theorem StoreRegion.storeOk {code : CodeMap} {mem : Ram} {region : MemoryRegion}
    (h : StoreRegion code mem region) {addr : BitVec 64} {len : Nat}
    {p : BitVec 64} {codeLen : Nat}
    (hin : InRegion region addr len) (hap : RangeApart addr len p codeLen) :
    Instructions.StorePre.StoreOk code mem addr len p codeLen := by
  refine ⟨?_, ?_, ?_, hap, ?_⟩
  · have hb : region.start + region.size < 2 ^ 32 := h.bounded
    exact Nat.le_trans hin.2.1 (Nat.le_of_lt hb)
  · intro i hi
    exact Option.isSome_iff_exists.mpr
      (h.allocated _ (StoreRegion.contains_byte hin hi))
  · intro i hi htable
    exact h.avoids _ (StoreRegion.contains_byte hin hi) (.inr htable)
  · intro x hx i hi heq
    exact h.avoids _ (StoreRegion.contains_byte hin hi) (.inl ⟨x.2, heq ▸ hx⟩)

theorem OutputFrameContract.of_valid {initial : RamState} {output : MemoryRegion}
    {reads : List MemoryRegion} {stackBytes : Nat}
    (hout : ValidOutput initial output) (hstack : Stack.Valid initial stackBytes)
    (hsep : MemorySeparation reads output (Stack.region initial stackBytes)) :
    OutputFrameContract Extracted.programImage initial.external output
      (Stack.region initial stackBytes) := by
  have ho := (hsep.2 output (by simp)).2
  have hs := (hsep.2 (Stack.region initial stackBytes) (by simp)).2
  exact ⟨⟨hout.2.1, hout.2.2, ho⟩, ⟨hstack.1, hstack.2.1, hs⟩⟩

theorem StoreRegion.of_frame {code : CodeMap} {original mem : Ram} {region : MemoryRegion}
    {regions : List MemoryRegion} (h : StoreRegion code original region)
    (hf : RamWriteFrame original mem regions) : StoreRegion code mem region := by
  refine ⟨h.bounded, ?_, h.avoids⟩
  intro a ha
  exact Option.isSome_iff_exists.mp
    (hf.present a (Option.isSome_iff_exists.mpr (h.allocated a ha)))

end Sha1.Proofs.Common
