import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem inputSlice [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length offset count : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length)
    (source : s.regValue .rsi = ptr + BitVec.ofNat 64 offset) (fit : offset + count ≤ info.size) :
    (registerRegion s .rsi count).Bounded ∧ (registerRegion s .rsi count).Allocated s.external ∧
    (registerRegion s .rsi count).Disjoint (Stack.region entry 2264) ∧
    (registerRegion s .rsi count).HasBytes s.external (info.extract offset (offset + count)) := by
  let input : MemoryRegion := ⟨ptr.toNat, info.size⟩
  have valid := pre.infoBytes pos limit
  have bounded : ptr.toNat + info.size < 2^32 := valid.1
  have apart (r) (hr : r ∈ #v[registerRegion entry .rcx length, Stack.region entry 2264]) :
      input.Disjoint r := ((pre.separation pos limit).2 r hr).1 input (by simp [input])
  have bytes := frame_hasBytes (region := input) saved.frame (by
    intro r hr
    apply apart r
    simpa only [writtenLength, limit, ↓reduceIte] using hr)
    (by change ptr.toNat + info.size ≤ 2^64; omega) valid.2
  have addr : (s.regValue .rsi).toNat = ptr.toNat + offset := by
    rw [source, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]
  have lower {a : Nat} (inside : (registerRegion s .rsi count).Contains a) : input.Contains a := by
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + count at inside
    rw [addr] at inside
    change ptr.toNat ≤ a ∧ a < ptr.toNat + info.size
    omega
  have size : (info.extract offset (offset + count)).size = count := by
    rw [ByteArray.size_extract]
    omega
  refine ⟨?_, ?_, fun a ha ↦ apart _ (by simp) a (lower ha), size, ?_⟩
  · change (s.regValue .rsi).toNat + count < 2^32
    rw [addr]
    omega
  · intro a ha
    have hin := lower ha
    change ptr.toNat ≤ a.toNat ∧ a.toNat < ptr.toNat + info.size at hin
    let i : Fin info.size := ⟨a.toNat - ptr.toNat, by omega⟩
    have byte := bytes.2 i
    change s.external[BitVec.ofNat 64 (ptr.toNat + i.val)]? = _ at byte
    have eq : ptr.toNat + i.val = a.toNat := by dsimp only [i]; omega
    rw [eq, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    exact ⟨_, byte⟩
  · intro i
    have hi : i.val < count := Nat.lt_of_lt_of_eq i.isLt size
    have byte := bytes.2 ⟨offset + i.val, by omega⟩
    change s.external[BitVec.ofNat 64 ((s.regValue .rsi).toNat + i.val)]? = _
    rw [addr, Nat.add_assoc]
    simpa only [ByteArray.getElem_extract] using byte

end Hkdf.Proofs.NewExpand.Expand.Info
