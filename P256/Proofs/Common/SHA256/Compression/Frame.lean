import X86Proofs.Program.Compose
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

variable {p : BitVec 64} {codeLen hi : Nat} {s : RamState}

theorem frame_offset_toNat (frame : StackFramePre p codeLen 0 hi s)
    (off count : Nat) (bound : off + count ≤ hi) :
    (rspOf s + BitVec.ofNat 64 off).toNat = (rspOf s).toNat + off := by
  have top := frame.top
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem frame_readable (frame : StackFramePre p codeLen 0 hi s)
    (off count : Nat) (bound : off + count ≤ hi) :
    MemReadable s (rspOf s + BitVec.ofNat 64 off) count := by
  refine ⟨?_, ?_⟩
  · rw [frame_offset_toNat frame off count bound]
    have top := frame.top
    omega
  · intro i hi'
    have h := frame.present (off + i) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem frame_writable4 (frame : StackFramePre p codeLen 0 hi s)
    (off : Nat) (bound : off + 4 ≤ hi) (_aligned : off % 4 = 0) :
    MemWritable s (rspOf s + BitVec.ofNat 64 off) 4 := by
  have read := frame_readable frame off 4 bound
  have addr := frame_offset_toNat frame off 4 bound
  have bottom := frame.bottom
  refine ⟨read.low, read.mem, PageTableEntriesApart.of_frames (Or.inr ?_)⟩ <;> rw [addr] <;> omega

theorem frame_apart (frame : StackFramePre p codeLen 0 hi s)
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

end P256.Proofs.Common.SHA256.Compression
