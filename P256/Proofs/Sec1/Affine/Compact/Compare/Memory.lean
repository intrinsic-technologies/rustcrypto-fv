import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Compare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def clobbers (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.reg 13,.flags,.rip,
    .mem (stackPtr s-512) 8,.mem (stackPtr s-768) 8,.mem (stackPtr s-769) 1]

theorem stack_bytes {s t u : RamState} (g : AgreesExcept (clobbers s) t u)
    (offset len : Nat) (ho : offset≤760) (hl : len≤offset+8)
    (apart : offset+8≤512 ∨ 512+len≤offset) :
    ∀ i<len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?=
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  have addr : (stackPtr s-769#64)+BitVec.ofNat 64 (769-offset)=stackPtr s-BitVec.ofNat 64 offset := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 769 offset (by omega) (by omega)]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [← BitVec.add_assoc (-769#64) (769#64),
      show -769#64+769#64=0#64 from by decide,BitVec.zero_add]
  rw [← addr]
  apply Uncompressed.Output.bytes_of_offsets g (by omega)
  intro address count member
  simp only [clobbers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try cases h
  · refine ⟨257,?_,by decide,by omega⟩
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  · refine ⟨1,?_,by decide,by omega⟩
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  · exact ⟨0,by simp,by decide,by omega⟩

theorem stack_word {s t u : RamState} (g : AgreesExcept (clobbers s) t u)
    (offset : Nat) (ho : offset≤760) (apart : offset+8≤512 ∨ 520≤offset) :
    memLoad u.external (stackPtr s-BitVec.ofNat 64 offset) 64=
      memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro j hj
  exact congrArg (fun b : Option UInt8 ↦ b.getD 0)
    (stack_bytes g offset 8 ho (by omega) apart j hj)

end P256.Proofs.Sec1.Affine.Compact.Compare
