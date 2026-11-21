import X86Proofs.Program.Compose
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

structure FramePre (p : BitVec 64) (codeLen hi : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  align : (rspOf s).toNat % 8 = 0
  tables : (rspOf s).toNat + hi ≤ 0x1000 ∨ 0x3000 ≤ (rspOf s).toNat
  top : (rspOf s).toNat + hi ≤ 2 ^ 32
  present : ∀ i < hi, (s.external[rspOf s + BitVec.ofNat 64 i]?).isSome
  codeLow : p.toNat + codeLen ≤ 2 ^ 32
  codeApart : p.toNat + codeLen ≤ (rspOf s).toNat ∨ (rspOf s).toNat + hi ≤ p.toNat

variable {p : BitVec 64} {codeLen hi : Nat} {s : RamState}

theorem frame_offset_toNat (frame : FramePre p codeLen hi s)
    (off count : Nat) (bound : off + count ≤ hi) :
    (rspOf s + BitVec.ofNat 64 off).toNat = (rspOf s).toNat + off := by
  have top := frame.top
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem frame_readable (frame : FramePre p codeLen hi s)
    (off count : Nat) (bound : off + count ≤ hi) :
    MemReadable s (rspOf s + BitVec.ofNat 64 off) count := by
  refine ⟨?_, ?_⟩
  · rw [frame_offset_toNat frame off count bound]
    have top := frame.top
    omega
  · intro i hi'
    have h := frame.present (off + i) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem frame_writable4 (frame : FramePre p codeLen hi s)
    (off : Nat) (bound : off + 4 ≤ hi) (aligned : off % 4 = 0) :
    MemWritable s (rspOf s + BitVec.ofNat 64 off) 4 := by
  have read := frame_readable frame off 4 bound
  have addr := frame_offset_toNat frame off 4 bound
  have bottom := frame.tables
  refine ⟨read.low, read.mem, ?_⟩
  unfold PageTableEntriesApart
  rw [addr]
  omega

theorem frame_apart (frame : FramePre p codeLen hi s)
    (off count pos len : Nat) (bound : off + count ≤ hi) (codeBound : pos + len ≤ codeLen) :
    RangeApart (rspOf s + BitVec.ofNat 64 off) count (p + BitVec.ofNat 64 pos) len := by
  have addr := frame_offset_toNat frame off count bound
  have top := frame.top
  have codeLow := frame.codeLow
  have apart := frame.codeApart
  apply RangeApart.of_toNat
  · rw [addr]
    omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [addr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

end P256.Proofs.SHA256.Compression
