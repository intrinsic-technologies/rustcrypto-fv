import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Common.Memory

open X86 X86.Machine X86Proofs

theorem loadBytes_loop_congr {before after : Ram} {address : BitVec 64}
    {count offset shift accumulator : Nat}
    (same : ∀ i < count,
      after[address + BitVec.ofNat 64 (offset + i)]? =
        before[address + BitVec.ofNat 64 (offset + i)]?) :
    loadBytes.loop after address count offset shift accumulator =
      loadBytes.loop before address count offset shift accumulator := by
  induction count generalizing offset shift accumulator with
  | zero => rfl
  | succ count ih =>
    simp only [loadBytes.loop, addAddress, fromNat]
    rw [show after[address + BitVec.ofNat 64 offset]? =
      before[address + BitVec.ofNat 64 offset]? from by simpa using same 0 (by omega)]
    cases before[address + BitVec.ofNat 64 offset]? with
    | none => rfl
    | some byte =>
      apply ih
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using same (i + 1) (by omega)

theorem loadBytes_congr {before after : Ram} {address : BitVec 64} {count : Nat}
    (same : ∀ i < count,
      after[address + BitVec.ofNat 64 i]? = before[address + BitVec.ofNat 64 i]?) :
    loadBytes after address count = loadBytes before address count :=
by
  apply loadBytes_loop_congr
  simpa only [Nat.zero_add] using same

theorem loadBytes_loop_allocated {memory : Ram} {address : BitVec 64}
    {count offset shift accumulator : Nat} {value : BitVec 64}
    (loaded : loadBytes.loop memory address count offset shift accumulator = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 (offset + i)]?).isSome := by
  induction count generalizing offset shift accumulator with
  | zero => intro i hi; omega
  | succ count ih =>
    simp only [loadBytes.loop, addAddress, fromNat] at loaded
    split at loaded
    · contradiction
    · rename_i byte found
      intro i hi
      by_cases zero : i = 0
      · subst i
        simpa only [Nat.add_zero, found] using (show (some byte).isSome from rfl)
      · have tail := ih loaded (i - 1) (by omega)
        simpa only [show offset + 1 + (i - 1) = offset + i by omega] using tail

theorem loadBytes_allocated {memory : Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (loaded : loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome :=
by
  simpa only [Nat.zero_add] using loadBytes_loop_allocated loaded

theorem bytes_of_loadBytes64 {memory : Ram} {address : BitVec 64} {value : BitVec 64}
    (loaded : loadBytes memory address 8 = .ok value) :
    Bytes memory address 8 (storedByte value) := by
  have bytes := Bytes.of_memLoad (n := 64) (loadBytes_allocated loaded)
  have same : memLoad memory address 64 = value :=
    Except.ok.inj (bytes.loadBytes64.symm.trans loaded)
  simpa only [same] using bytes

theorem memLoad_of_loadBytes64 {memory : Ram} {address : BitVec 64} {value : BitVec 64}
    (loaded : loadBytes memory address 8 = .ok value) :
    memLoad memory address 64 = value :=
  (bytes_of_loadBytes64 loaded).memLoad (by decide) (by decide)

end Sha2.Proofs.Common.Memory
