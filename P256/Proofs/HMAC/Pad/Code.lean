import P256.Proofs.HMAC.Pad.Interface
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem mode_valid (loop : Loop) (i : Nat) : (loop.mode i).Valid := by
  simp [Loop.mode, AddrMode.Valid, regLow]

theorem mode_rexX (loop : Loop) (i : Nat) : (loop.mode i).rexX = 0 := rfl

theorem mode_rexB (loop : Loop) (i : Nat) : (loop.mode i).rexB = 0 := rfl

theorem disp_value (loop : Loop) (i : Nat) (hi : i < 4) :
    3#64 + (loop.disp i).value = BitVec.ofNat 64 loop.offset + BitVec.ofNat 64 i := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases loop <;> decide +kernel

theorem mode_address (loop : Loop) {s : RamState} (i n : Nat) (hi : i < 4)
    (counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + 3)) (next : BitVec 64) :
    (loop.mode i).addr s next = buffer loop s + BitVec.ofNat 64 (4 * n + i) := by
  change stackPtr s + (s.regValue .rax <<< 0) + (loop.disp i).value = _
  rw [BitVec.shiftLeft_zero, counter, BitVec.ofNat_add]
  rw [BitVec.add_assoc, BitVec.add_assoc, disp_value loop i hi]
  simp only [buffer, BitVec.ofNat_add]
  ac_rfl

theorem xor_length (loop : Loop) (i : Nat) (hi : i < 4) :
    loop.position i + (3 + (loop.mode i).tail.length) = loop.position (i + 1) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases loop <;> decide +kernel

theorem xor_next (loop : Loop) (i : Nat) (hi : i < 4) :
    loop.address i + BitVec.ofNat 64 (3 + (loop.mode i).tail.length) = loop.address (i + 1) := by
  simp only [Loop.address, ← BitVec.ofNat_add, Nat.add_assoc, xor_length loop i hi]

theorem slice_at {s : RamState} (loaded : ProgramLoaded s) (address : Nat)
    (bytes : List UInt8) (start : 0x100000 ≤ address)
    (bound : address - 0x100000 + bytes.length ≤ 118431)
    (encoding : Extracted.textBytes.toListFrom (address - 0x100000) bytes.length = bytes) :
    CodeIn (codeRange (BitVec.ofNat 64 address) bytes) s := by
  have h := programText_slice (programLoaded_codeIn loaded) (address - 0x100000) bytes bound encoding
  have he : Extracted.textAddress + BitVec.ofNat 64 (address - 0x100000) =
      BitVec.ofNat 64 address := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (address - 0x100000) = _
    rw [← BitVec.ofNat_add, Nat.add_sub_of_le start]
  rwa [he] at h

theorem xor_code {s : RamState} (loaded : ProgramLoaded s) (loop : Loop)
    (i : Nat) (hi : i < 4) :
    CodeIn (codeRange (loop.address i)
      (0x80 :: (loop.mode i).modrm 6 :: ((loop.mode i).tail ++ [loop.mask]))) s := by
  apply slice_at loaded (loop.entry + loop.position i)
  all_goals rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases loop <;> decide +kernel

theorem add_code {s : RamState} (loaded : ProgramLoaded s) (loop : Loop) :
    CodeIn (codeRange (loop.address 4) [0x48, 0x83, 0xc0, 4]) s := by
  apply slice_at loaded (loop.entry + loop.position 4)
  all_goals cases loop <;> decide +kernel

theorem cmp_code {s : RamState} (loaded : ProgramLoaded s) (loop : Loop) :
    CodeIn (codeRange (loop.address 4 + 4) [0x48, 0x83, 0xf8, 67]) s := by
  change CodeIn (codeRange (BitVec.ofNat 64 (loop.entry + loop.position 4) + BitVec.ofNat 64 4) _) s
  rw [← BitVec.ofNat_add]
  apply slice_at loaded (loop.entry + loop.position 4 + 4)
  all_goals cases loop <;> decide +kernel

def Loop.back (loop : Loop) : BitVec 8 := -BitVec.ofNat 8 loop.length

theorem branch_code {s : RamState} (loaded : ProgramLoaded s) (loop : Loop) :
    CodeIn (codeRange (loop.address 4 + 8) [0x75, UInt8.ofBitVec loop.back]) s := by
  change CodeIn (codeRange (BitVec.ofNat 64 (loop.entry + loop.position 4) + BitVec.ofNat 64 8) _) s
  rw [← BitVec.ofNat_add]
  apply slice_at loaded (loop.entry + loop.position 4 + 8)
  all_goals cases loop <;> decide +kernel

theorem branch_target (loop : Loop) :
    loop.address 4 + 8 + 2 + loop.back.signExtend 64 = BitVec.ofNat 64 loop.entry := by
  cases loop <;> decide +kernel

theorem branch_end (loop : Loop) :
    loop.address 4 + 8 + 2 = BitVec.ofNat 64 (loop.entry + loop.length) := by
  cases loop <;> rfl

theorem address_inProgram (loop : Loop) (offset : Nat) (bound : offset ≤ loop.length) :
    InProgram (BitVec.ofNat 64 (loop.entry + offset)) := by
  have h := inProgram_of_textOffset (loop.entry + offset - 0x100000) (by
    cases loop <;> simp only [Loop.entry, Loop.length, Loop.position, Nat.lt_irrefl, reduceIte] at bound ⊢ <;> omega)
  have start : 0x100000 ≤ loop.entry := by cases loop <;> decide
  have he : Extracted.textAddress + BitVec.ofNat 64 (loop.entry + offset - 0x100000) =
      BitVec.ofNat 64 (loop.entry + offset) := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (loop.entry + offset - 0x100000) = _
    rw [← BitVec.ofNat_add, Nat.add_sub_of_le (by omega)]
  rwa [he] at h

theorem position_le (loop : Loop) (i : Nat) (hi : i ≤ 4) : loop.position i ≤ loop.length := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    cases loop <;> decide

end P256.Proofs.HMAC.Pad
