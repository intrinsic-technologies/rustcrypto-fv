import P256.Proofs.Program.Memory
import P256.Proofs.Common.Memory.LoadBytes

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem singleton_input {slices : Array Input} {input : ByteArray}
    (h : inputBytes slices = #[input]) :
    ∃ address, slices = #[Input.mk address input] := by
  obtain ⟨⟨address, bytes⟩, hs, hb⟩ := Array.map_eq_singleton_iff.mp h
  cases hb
  exact ⟨address, hs⟩

theorem word64_memReadable {s : RamState} {address value : BitVec 64}
    (hbound : (MemoryRegion.mk address.toNat 8).Bounded)
    (hword : (MemoryRegion.mk address.toNat 8).Word64At s.external value) :
    MemReadable s address 8 := by
  have hl : loadBytes s.external address 8 = .ok value := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hword.2
  exact ⟨Nat.le_of_lt hbound, P256.Proofs.Common.Memory.allocated_of_loadBytes hl⟩

theorem word64_memLoad {s : RamState} {address value : BitVec 64}
    (hword : (MemoryRegion.mk address.toNat 8).Word64At s.external value) :
    memLoad s.external address 64 = value := by
  have hl : loadBytes s.external address 8 = .ok value := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hword.2
  exact (P256.Proofs.Common.Memory.bytes_of_loadBytes64
    (P256.Proofs.Common.Memory.allocated_of_loadBytes hl) hl).memLoad (by decide) (by decide)

theorem hasBytes_allocated {region : MemoryRegion} {memory : Ram} {input : ByteArray}
    (h : region.HasBytes memory input) : region.Allocated memory := by
  intro a ha
  have lo : region.start ≤ a.toNat := ha.1
  have hi : a.toNat - region.start < input.size := by
    have he : input.size = region.size := h.1
    have upper : a.toNat < region.start + region.size := ha.2
    omega
  have byte := h.2 ⟨a.toNat - region.start, hi⟩
  have he : region.start + (a.toNat - region.start) = a.toNat := Nat.add_sub_of_le lo
  refine ⟨input[a.toNat - region.start]'hi, ?_⟩
  simpa only [he, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte

theorem hasBytes_memReadable {s : RamState} {address : BitVec 64} {input : ByteArray}
    {size : Nat} (hbound : (MemoryRegion.mk address.toNat size).Bounded)
    (hbytes : (MemoryRegion.mk address.toNat size).HasBytes s.external input) :
    MemReadable s address size := by
  refine ⟨Nat.le_of_lt hbound, ?_⟩
  intro i hi
  have hs : input.size = size := hbytes.1
  have hb := hbytes.2 ⟨i, by omega⟩
  change s.external[BitVec.ofNat 64 (address.toNat + i)]? = _ at hb
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  simp only [hb, Option.isSome_some]

theorem tableEntry_registerRegion {s : RamState} {reg : Syntax.Reg} {count i : Nat}
    (hb : (registerRegion s reg (8 * count)).Bounded) (hi : i < count) :
    tableEntry (registerRegion s reg (8 * count)) i =
      MemoryRegion.mk (s.regValue reg + BitVec.ofNat 64 (8 * i)).toNat 8 := by
  have hb' : (s.regValue reg).toNat + 8 * count < 2^32 := hb
  have he : (s.regValue reg + BitVec.ofNat 64 (8 * i)).toNat =
      (s.regValue reg).toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [tableEntry, registerRegion, he]

theorem input_memReadable {s : RamState} {slices : Array Input}
    (h : ValidInputs s slices) (i : Fin slices.size) :
    MemReadable s slices[i].address slices[i].bytes.size :=
  hasBytes_memReadable (h.slicesValid i).2.2.2.1 (h.slicesValid i).2.2.2.2

theorem input_pointer_memLoad {s : RamState} {slices : Array Input}
    (h : ValidInputs s slices) (i : Fin slices.size) :
    memLoad s.external (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 64 =
      slices[i].address := by
  have hw := (h.slicesValid i).1
  rw [pointerTable, tableEntry_registerRegion h.pointerTableValid.2 i.isLt] at hw
  exact word64_memLoad hw

theorem input_length_memLoad {s : RamState} {slices : Array Input}
    (h : ValidInputs s slices) (i : Fin slices.size) :
    memLoad s.external (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 64 =
      BitVec.ofNat 64 slices[i].bytes.size := by
  have hw := (h.slicesValid i).2.1
  rw [lengthTable, tableEntry_registerRegion h.lengthTableValid.2 i.isLt] at hw
  exact word64_memLoad hw

theorem tableEntry_memReadable {s : RamState} {reg : Syntax.Reg} {count i : Nat}
    {value : BitVec 64} (hb : (registerRegion s reg (8 * count)).Bounded) (hi : i < count)
    (hw : (tableEntry (registerRegion s reg (8 * count)) i).Word64At s.external value) :
    MemReadable s (s.regValue reg + BitVec.ofNat 64 (8 * i)) 8 := by
  have he : (tableEntry (registerRegion s reg (8 * count)) i).Bounded := by
    have ht : (s.regValue reg).toNat + 8 * count < 2^32 := hb
    change (s.regValue reg).toNat + 8 * i + 8 < 2^32
    omega
  rw [tableEntry_registerRegion hb hi] at hw he
  exact word64_memReadable he hw

theorem input_pointer_memReadable {s : RamState} {slices : Array Input}
    (h : ValidInputs s slices) (i : Fin slices.size) :
    MemReadable s (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 :=
  tableEntry_memReadable h.pointerTableValid.2 i.isLt (h.slicesValid i).1

theorem input_length_memReadable {s : RamState} {slices : Array Input}
    (h : ValidInputs s slices) (i : Fin slices.size) :
    MemReadable s (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 8 :=
  tableEntry_memReadable h.lengthTableValid.2 i.isLt (h.slicesValid i).2.1

end P256.Proofs.Program
