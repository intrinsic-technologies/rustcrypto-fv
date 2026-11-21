import Md5.Spec.Program
import X86Proofs.Program.ReadWrite.Bytes
import Init.Data.Array.Extract
import Init.Data.ByteArray.Lemmas

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86Proofs

theorem message_empty : Slices.message #[] = ByteArray.empty := rfl

theorem message_push (inputs : Array Slices.Input) (input : Slices.Input) :
    Slices.message (inputs.push input) = Slices.message inputs ++ input.bytes := by
  exact Array.foldl_push

theorem message_foldl (inputs : Array Slices.Input) (initial : ByteArray) :
    inputs.foldl (fun message input ↦ message ++ input.bytes) initial =
      initial ++ Slices.message inputs := by
  have h := Array.foldl_hom (fun bytes ↦ initial ++ bytes)
    (xs := inputs) (init := ByteArray.empty)
    (g₁ := fun message input ↦ message ++ input.bytes)
    (g₂ := fun message input ↦ message ++ input.bytes)
    (fun _ _ ↦ ByteArray.append_assoc)
  simpa only [ByteArray.append_empty, Slices.message] using h

theorem message_append (left right : Array Slices.Input) :
    Slices.message (left ++ right) = Slices.message left ++ Slices.message right := by
  exact Array.foldl_append.trans (message_foldl right (Slices.message left))

theorem message_extract_succ (inputs : Array Slices.Input) (start i : Nat)
    (hstart : start ≤ i) (hi : i < inputs.size) :
    Slices.message (inputs.extract start (i + 1)) =
      Slices.message (inputs.extract start i) ++ inputs[i].bytes := by
  rw [Array.extract_succ_right (by omega) hi, message_push]

theorem message_prefix_succ (inputs : Array Slices.Input) (i : Nat) (hi : i < inputs.size) :
    Slices.message (inputs.extract 0 (i + 1)) =
      Slices.message (inputs.extract 0 i) ++ inputs[i].bytes :=
  message_extract_succ inputs 0 i (Nat.zero_le _) hi

theorem extract_clamp_stop (inputs : Array Slices.Input) (start stop : Nat) :
    inputs.extract start (min stop inputs.size) = inputs.extract start stop := by
  apply Array.extract_eq_extract_right.mpr
  omega

theorem extract_clamp_start (inputs : Array Slices.Input) (start stop : Nat) :
    inputs.extract (min start inputs.size) stop = inputs.extract start stop := by
  apply Array.extract_eq_extract_left.mpr
  omega

theorem message_prefix_clamp (inputs : Array Slices.Input) (first : Nat) :
    Slices.message (inputs.extract 0 (min first inputs.size)) =
      Slices.message (inputs.extract 0 first) := by
  rw [extract_clamp_stop]

theorem message_suffix_clamp (inputs : Array Slices.Input) (first : Nat) :
    Slices.message (inputs.extract (min first inputs.size) inputs.size) =
      Slices.message (inputs.extract first inputs.size) := by
  rw [extract_clamp_start]

theorem message_prefix_of_size_le (inputs : Array Slices.Input) (first : Nat)
    (h : inputs.size ≤ first) :
    Slices.message (inputs.extract 0 first) = Slices.message inputs := by
  rw [Array.extract_eq_self_of_le h]

theorem message_suffix_of_size_le (inputs : Array Slices.Input) (first : Nat)
    (h : inputs.size ≤ first) :
    Slices.message (inputs.extract first inputs.size) = ByteArray.empty := by
  rw [Array.extract_empty_of_size_le_start h, message_empty]

theorem message_split (inputs : Array Slices.Input) (first : Nat) :
    Slices.message (inputs.extract 0 first) ++
        Slices.message (inputs.extract first inputs.size) = Slices.message inputs := by
  rw [← message_append, Array.extract_append_extract, Nat.zero_min]
  rw [Array.extract_eq_self_of_le (Nat.le_max_right ..)]

theorem size_message (inputs : Array Slices.Input) :
    (Slices.message inputs).size = inputs.foldl (fun size input ↦ size + input.bytes.size) 0 := by
  exact (Array.foldl_hom ByteArray.size (xs := inputs) (init := ByteArray.empty)
    (fun _ _ ↦ ByteArray.size_append.symm)).symm

theorem size_message_le (inputs : Array Slices.Input) (bound : Nat)
    (h : ∀ i : Fin inputs.size, inputs[i].bytes.size ≤ bound) :
    (Slices.message inputs).size ≤ inputs.size * bound := by
  unfold Slices.message
  apply Array.foldl_induction (motive := fun i (bytes : ByteArray) ↦ bytes.size ≤ i * bound)
  · simp only [ByteArray.size_empty, Nat.zero_mul, Nat.le_refl]
  · intro i bytes hbytes
    simpa only [ByteArray.size_append, Nat.add_mul, Nat.one_mul] using
      Nat.add_le_add hbytes (h i)

theorem validInputs_size_lt {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) : inputs.size < 2^29 := by
  have htable := h.pointerTableValid.2
  change (s.regValue .rdi).toNat + 8 * inputs.size < 2^32 at htable
  omega

theorem validInputs_bytes_size_lt {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) : inputs[i].bytes.size < 2^32 := by
  have hinput := (h.slicesValid i).2.2.2.1
  change inputs[i].address.toNat + inputs[i].bytes.size < 2^32 at hinput
  omega

theorem validInputs_message_size_lt {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) : (Slices.message inputs).size < 2^61 := by
  have hsize := validInputs_size_lt h
  have hmessage := size_message_le inputs (2^32 - 1) (fun i ↦ by
    have hi := validInputs_bytes_size_lt h i
    omega)
  omega

theorem size_message_prefix_le (inputs : Array Slices.Input) (first : Nat) :
    (Slices.message (inputs.extract 0 first)).size ≤ (Slices.message inputs).size := by
  have h := congrArg ByteArray.size (message_split inputs first)
  rw [ByteArray.size_append] at h
  omega

theorem size_message_suffix_le (inputs : Array Slices.Input) (first : Nat) :
    (Slices.message (inputs.extract first inputs.size)).size ≤ (Slices.message inputs).size := by
  have h := congrArg ByteArray.size (message_split inputs first)
  rw [ByteArray.size_append] at h
  omega

theorem size_message_extract_le (inputs : Array Slices.Input) (start stop : Nat) :
    (Slices.message (inputs.extract start stop)).size ≤ (Slices.message inputs).size := by
  have h := congrArg (fun slices ↦ (Slices.message slices).size)
    (Array.extract_append_extract (as := inputs) (i := 0) (j := start) (k := stop))
  simp only [message_append, ByteArray.size_append, Nat.zero_min] at h
  have hprefix := size_message_prefix_le inputs (max start stop)
  omega

theorem validInputs_message_extract_size_lt {s : Machine.RamState}
    {inputs : Array Slices.Input} (h : Slices.ValidInputs s inputs) (start stop : Nat) :
    (Slices.message (inputs.extract start stop)).size < 2^61 :=
  Nat.lt_of_le_of_lt (size_message_extract_le inputs start stop) (validInputs_message_size_lt h)

theorem validInputs_pointer_load {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    Machine.loadBytes s.external (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 =
      .ok inputs[i].address := by
  have hload := (h.slicesValid i).2.1.2
  simpa only [Slices.tableEntry, Slices.pointerTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using hload

theorem validInputs_length_load {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    Machine.loadBytes s.external (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 8 =
      .ok (BitVec.ofNat 64 inputs[i].bytes.size) := by
  have hload := (h.slicesValid i).2.2.1.2
  simpa only [Slices.tableEntry, Slices.lengthTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using hload

private theorem loadBytes_loop_isSome {memory : Machine.Ram} {address : BitVec 64}
    {remaining current shift accumulator : Nat} {value : BitVec 64}
    (h : Machine.loadBytes.loop memory address remaining current shift accumulator = .ok value) :
    ∀ i < remaining, (memory[address + BitVec.ofNat 64 (current + i)]?).isSome := by
  induction remaining generalizing current shift accumulator with
  | zero => intro i hi; omega
  | succ remaining ih =>
    cases hbyte : memory[Machine.addAddress address current]? with
    | none => simp only [Machine.loadBytes.loop, hbyte] at h; cases h
    | some byte =>
      simp only [Machine.loadBytes.loop, hbyte] at h
      intro i hi
      cases i with
      | zero =>
        change memory[address + BitVec.ofNat 64 current]? = some byte at hbyte
        simpa only [Nat.add_zero, hbyte] using (show (some byte).isSome = true from rfl)
      | succ i =>
        have hb := ih h i (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hb

theorem loadBytes_isSome {memory : Machine.Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : Machine.loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome := by
  simpa only [Nat.zero_add] using loadBytes_loop_isSome h

theorem word64At_memLoad {region : MemoryRegion} {memory : Machine.Ram} {value : BitVec 64}
    (h : region.Word64At memory value) :
    memLoad memory (BitVec.ofNat 64 region.start) 64 = value := by
  have hb : Bytes memory (BitVec.ofNat 64 region.start) 8
      (storedByte (memLoad memory (BitVec.ofNat 64 region.start) 64)) :=
    Bytes.of_memLoad (n := 64) (loadBytes_isSome h.2)
  exact Except.ok.inj (hb.loadBytes64.symm.trans h.2)

theorem validInputs_pointer_read {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s =
      inputs[i].address := by
  have hread := word64At_memLoad (h.slicesValid i).2.1
  simpa only [Operand.read, Slices.tableEntry, Slices.pointerTable, registerRegion,
    BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hread

theorem validInputs_length_read {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s =
      BitVec.ofNat 64 inputs[i].bytes.size := by
  have hread := word64At_memLoad (h.slicesValid i).2.2.1
  simpa only [Operand.read, Slices.tableEntry, Slices.lengthTable, registerRegion,
    BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hread

theorem tableEntry_contains {table : MemoryRegion} {i address : Nat}
    (hentry : 8 * (i + 1) ≤ table.size)
    (h : (Slices.tableEntry table i).Contains address) : table.Contains address := by
  change table.start + 8 * i ≤ address ∧ address < table.start + 8 * i + 8 at h
  constructor <;> omega

theorem tableEntry_bounded {table : MemoryRegion} {i : Nat}
    (hentry : 8 * (i + 1) ≤ table.size) (h : table.Bounded) :
    (Slices.tableEntry table i).Bounded := by
  change table.start + 8 * i + 8 < userAddressLimit
  unfold MemoryRegion.Bounded at h
  omega

theorem word64At_readable {s : Machine.RamState} {region : MemoryRegion} {value : BitVec 64}
    (h : region.Word64At s.external value) (hb : region.Bounded) :
    MemReadable s (BitVec.ofNat 64 region.start) 8 := by
  refine ⟨?_, loadBytes_isSome h.2⟩
  have hsize : 8 = region.size := h.1
  change region.start + region.size < 2^32 at hb
  simp only [BitVec.toNat_ofNat]
  omega

theorem validInputs_pointer_readable {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    MemReadable s (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 := by
  have hb := word64At_readable (h.slicesValid i).2.1
    (tableEntry_bounded (by change 8 * (i.val + 1) ≤ 8 * inputs.size; omega)
      h.pointerTableValid.2)
  simpa only [Slices.tableEntry, Slices.pointerTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

theorem validInputs_length_readable {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    MemReadable s (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 8 := by
  have hb := word64At_readable (h.slicesValid i).2.2.1
    (tableEntry_bounded (by change 8 * (i.val + 1) ≤ 8 * inputs.size; omega)
      h.lengthTableValid.2)
  simpa only [Slices.tableEntry, Slices.lengthTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

theorem validInputs_bytes_readable {s : Machine.RamState} {inputs : Array Slices.Input}
    (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    MemReadable s inputs[i].address inputs[i].bytes.size := by
  refine ⟨?_, ?_⟩
  · have hb := (h.slicesValid i).2.2.2.1
    change inputs[i].address.toNat + inputs[i].bytes.size < 2^32 at hb
    omega
  · intro j hj
    have hjmem := (h.slicesValid i).2.2.2.2.2 ⟨j, hj⟩
    have he : BitVec.ofNat 64 (inputs[i].region.start + j) =
        inputs[i].address + BitVec.ofNat 64 j := by
      simp only [Slices.Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [he] at hjmem
    rw [hjmem]
    rfl

end Md5.Proofs.Streaming
