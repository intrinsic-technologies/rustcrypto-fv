import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Preconditions

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem program_text_range (offset length : Nat)
    (h : offset + length ≤ Extracted.textBytes.size) :
    ∀ i < length, InProgram
      ((Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (offset + i) (by omega)

variable {s : RamState} {stack input : BitVec 64} {buffer : Standards.RFC.MD5.Buffer}
  {words : Vector (BitVec 32) 16}

theorem LoopData.readable_input (h : LoopData stack input buffer words s)
    (offset length : Nat) (hBound : offset + length ≤ 64) :
    MemReadable s (input + BitVec.ofNat 64 offset) length :=
  MemoryRoutines.memReadable_slice h.readable offset length hBound

theorem LoopData.readable_stack (h : LoopData stack input buffer words s)
    (offset length : Nat) (hBound : offset + length ≤ 136) :
    MemReadable s (stack + BitVec.ofNat 64 offset) length :=
  MemoryRoutines.memReadable_slice h.frame.readable offset length hBound

theorem LoopData.store_stack (h : LoopData stack input buffer words s)
    {p : BitVec 64} {codeLen offset length : Nat} {addr : RamState → BitVec 64}
    (hRip : s.RIP = p) (hAddr : addr s = stack + BitVec.ofNat 64 offset)
    (hBound : offset + length ≤ 136)
    (hCode : ∀ i < codeLen, InProgram (p + BitVec.ofNat 64 i)) :
    Memory.StorePre p codeLen addr length s := by
  refine ⟨hRip, ?_, ?_⟩
  · rw [hAddr]
    exact memoryWritable_slice h.frame offset length hBound
  · rw [hAddr]
    intro i hi j hj he
    have ha : InProgram (stack + BitVec.ofNat 64 (offset + i)) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, he]
      exact hCode j hj
    exact h.code (offset + i) (by omega) ha

end Md5.Proofs.Block
