import P256.Proofs.Common.Der.Memory.Writable
import X86Proofs.Program.Compose

namespace P256.Proofs.Common.Der.Memory

open X86 X86.Machine X86.UserProcess X86Proofs

theorem MemWritable.of_agreesExcept {s t : RamState} {cs : List Component}
    {a : BitVec 64} {len : Nat} (h : MemWritable s a len) (ha : AgreesExcept cs s t) :
    MemWritable t a len :=
  ⟨h.low, fun i hi ↦ ha.grow _ (h.bytes i hi), h.tables⟩

@[x86_pre] theorem MemWritable.of_holds {e : Effect} {s t : RamState}
    {a : BitVec 64} {len : Nat} (h : e.Holds s t) (hm : MemWritable s a len) :
    MemWritable t a len :=
  hm.of_agreesExcept h.agrees

theorem MemWritable.carry {e : Effect} {s t : RamState}
    (h : e.Holds s t) (ho : Obs (e.after s true) t)
    {addr : RamState → BitVec 64} (ha : AddrObs addr) {len : Nat}
    (hw : MemWritable s (addr (e.after s true)) len) : MemWritable t (addr t) len := by
  rw [ha.eq ho]
  exact hw.of_holds h

@[x86_pre] theorem StorePre.of_holds {e : Effect} {s t : RamState}
    (h : e.Holds s t) (ho : Obs (e.after s true) t)
    {p : BitVec 64} {codeLen : Nat} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (ha : AddrObs addr)
    (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    StorePre p codeLen addr len t :=
  ⟨h.rip_of hrip, MemWritable.carry h ho ha hw, RangeApart.carry ho ha hap⟩

theorem MemWritable.slice {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (offset count : Nat) (hb : offset + count ≤ len) :
    MemWritable s (addr + BitVec.ofNat 64 offset) count := by
  have hl := h.low
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega),
      Nat.mod_eq_of_lt (show addr.toNat + offset < 2^64 by omega)]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.bytes (offset + i) (by omega)
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.tables (offset + i) (by omega)

end P256.Proofs.Common.Der.Memory
