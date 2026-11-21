import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Sec1.Decompress.Interface
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem coordinate_size {bytes : ByteArray} (size : bytes.size = 33) :
    (bytes.extract 1 33).size = 32 := by
  simp [ByteArray.size_extract, size]

theorem coordinate_address [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) :
    (s.regValue .rsi + 1).toNat = (s.regValue .rsi).toNat + 1 := by
  have low : (s.regValue .rsi).toNat + 65 < 2^32 := pre.inputBounded
  rw [BitVec.toNat_add]
  change ((s.regValue .rsi).toNat + 1) % 2^64 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem coordinate_bytes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (size : bytes.size = 33)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 80, Stack.region s 3360]) :
    (MemoryRegion.mk (s.regValue .rsi + 1).toNat 32).HasBytes t.external
      (bytes.extract 1 33) := by
  refine ⟨coordinate_size size, ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [coordinate_size size] using i.isLt
  have input := input_of_frame pre frame
  have value := input.2 (1 + i.val) (by omega)
  have within : 1 + i.val < bytes.data.size := by change _ < bytes.size; omega
  simp only [Array.getElem?_eq_getElem within, Option.getD_some] at value
  change t.external[BitVec.ofNat 64 ((s.regValue .rsi + 1).toNat + i.val)]? = _
  rw [coordinate_address pre]
  simpa only [ByteArray.getElem_extract, ByteArray.getElem_eq_getElem_data, ByteArray.data_extract, Array.getElem_extract, Nat.add_assoc, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using value

def decompressionLayout (offset : Nat) (above : offset + 8 ≤ 768) (enough : 80 ≤ offset + 8) :
    StackBufferLayout 3360 80 2592 :=
  ⟨768, offset, by decide, by decide, above, enough⟩

theorem decompression_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : AffineDecodePre s boundary bytes)
    (size : bytes.size = 33) (state : ScalarFrame.FrameState s t 80 3360 768)
    (rip : t.RIP = 0x10fc00) (input : t.regValue .rsi = s.regValue .rsi + 1)
    {offset : Nat} (above : offset + 8 ≤ 768) (enough : 80 ≤ offset + 8)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 offset)
    (parity : t.regValue .rdx = BitVec.ofNat 64 odd.toNat)
    (ret : InProgram (returnBoundary t).rip) : Decompress.Pre t boundary (bytes.extract 1 33) odd := by
  have low : (s.regValue .rsi).toNat + 65 < 2^32 := pre.inputBounded
  have sub (a : Nat) (ha : (registerRegion t .rsi 32).Contains a) :
      (registerRegion s .rsi 65).Contains a := by
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + 32 at ha
    rw [input, coordinate_address pre] at ha
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 65
    constructor <;> omega
  have cp : CalleePre t boundary 0x10fc00 32 80 2592 := by
    apply CalleePre.of_disjoint_input_and_stack (decompressionLayout offset above enough) pre.stack
      (pre.avoids _ (by simp)) state.bindingsSupported state.machine state.directionFlag
      state.loaded rip state.rsp _ _ _ output state.allocated pre.outerBoundary ret
    · change (t.regValue .rsi).toNat + 32 < 2^32
      rw [input, coordinate_address pre]
      omega
    · intro a ha
      exact Option.isSome_iff_exists.mp (state.allocated a
        (Option.isSome_iff_exists.mpr (pre.inputAllocated a (sub a.toNat ha))))
    · intro a ha hb
      exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (sub a ha) hb
  refine ⟨cp, ?_, coordinate_size size, parity⟩
  simpa only [registerRegion, input] using coordinate_bytes pre size state.frame

end P256.Proofs.Sec1.Affine.Compressed
