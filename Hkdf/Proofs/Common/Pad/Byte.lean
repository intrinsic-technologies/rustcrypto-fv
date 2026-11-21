import Hkdf.Proofs.Common.Pad.Memory
import Hkdf.Proofs.Common.Pad.Buffer
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions.CrossPageStore

def fin4 (i : Nat) (hi : i < 4) : Fin 4 := ⟨i, hi⟩

def address (v : Variant) : Nat → BitVec 64
  | 0 => v.entry
  | 1 => v.pc 1
  | 2 => v.pc 2
  | 3 => v.pc 3
  | 4 => v.addPC
  | _ => v.exit

structure Position (v : Variant) (s : RamState) (n i : Nat)
    (bytes : Vector UInt8 64) : Prop
    extends Memory v s where
  rip : s.RIP = address v i
  counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + (layout v).first)
  stored : Stored s (buffer v s) bytes (layout v).mask (4 * n + i)

theorem mode_valid (v : Variant) (i : Nat) (hi : i < 4) : (v.am (fin4 i hi)).Valid := by
  simp [Variant.am, AddrMode.Valid, regLow]

theorem mode_rexX (v : Variant) (i : Nat) (hi : i < 4) : (v.am (fin4 i hi)).rexX = 0 := rfl

theorem mode_rexB (v : Variant) (i : Nat) (hi : i < 4) : (v.am (fin4 i hi)).rexB = 0 := rfl

theorem disp_value (v : Variant) (i : Nat) (hi : i < 4) :
    BitVec.ofNat 64 (layout v).first + (layout v).displacement[fin4 i hi].value =
      BitVec.ofNat 64 ((layout v).bufferOffset + i) := by
  have h := (layout_valid v).displacement ⟨i, by omega⟩
  rw [← h]
  ac_rfl

theorem mode_address (v : Variant) {s : RamState} (i n : Nat) (hi : i < 4)
    (counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + (layout v).first))
    (next : BitVec 64) :
    (v.am (fin4 i hi)).addr s next = buffer v s + BitVec.ofNat 64 (4 * n + i) := by
  change stackPtr s + (s.regValue .rax <<< 0) + (layout v).displacement[fin4 i hi].value = _
  rw [BitVec.shiftLeft_zero, counter, BitVec.ofNat_add]
  rw [BitVec.add_assoc, BitVec.add_assoc, disp_value v i hi]
  simp only [buffer, BitVec.ofNat_add]
  ac_rfl

theorem xor_length (v : Variant) (i : Nat) (hi : i < 4) :
    (layout v).positions[i] + (3 + (v.am (fin4 i hi)).tail.length) =
      (layout v).positions[i + 1] := by
  have h := (layout_valid v).next (fin4 i hi)
  simpa [fin4, Variant.xorLength, Variant.am] using h.symm

theorem address_eq (v : Variant) (i : Nat) (hi : i ≤ 4) :
    address v i = Hkdf.Spec.Program.Extracted.textAddress +
      BitVec.ofNat 64 ((layout v).offset + (layout v).positions[i]) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with
    rfl | rfl | rfl | rfl | rfl <;> rfl

theorem address_inProgram_index (v : Variant) (i : Nat) (hi : i ≤ 4) :
    InProgram (address v i) := by
  rw [address_eq v i hi]
  exact inProgram_of_textOffset ((layout v).offset + (layout v).positions[i]) (by
    have bound := (layout_valid v).bound
    have pos : (layout v).positions[i] ≤ (layout v).positions[4] := by
      simpa only [Fin.getElem_fin] using (layout_valid v).positions ⟨i, by omega⟩
    omega)

theorem address_entry_offset (v : Variant) (i : Nat) (hi : i ≤ 4) :
    address v i = v.entry + BitVec.ofNat 64 (layout v).positions[i] := by
  rw [address_eq v i hi]
  simp [Variant.entry, Variant.pc, (layout_valid v).initial, BitVec.add_assoc,
    ← BitVec.ofNat_add]

theorem xor_next (v : Variant) (i : Nat) (hi : i < 4) :
    address v i + BitVec.ofNat 64 (3 + (v.am (fin4 i hi)).tail.length) = address v (i + 1) := by
  rw [address_eq v i (by omega), address_eq v (i + 1) (by omega)]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have h := xor_length v i hi
  have hn : (layout v).offset + (layout v).positions[i] +
      (3 + (v.am (fin4 i hi)).tail.length) =
      (layout v).offset + (layout v).positions[i + 1] := by
    calc
      (layout v).offset + (layout v).positions[i] +
          (3 + (v.am (fin4 i hi)).tail.length) =
          (layout v).offset + ((layout v).positions[i] +
            (3 + (v.am (fin4 i hi)).tail.length)) := by omega
      _ = (layout v).offset + (layout v).positions[i + 1] := by rw [h]
  rw [hn]

theorem xor_code {s : RamState} (loaded : ProgramLoaded s) (v : Variant)
    (i : Nat) (hi : i < 4) :
    CodeIn (codeRange (address v i)
      (0x80 :: (v.am (fin4 i hi)).modrm 6 ::
        ((v.am (fin4 i hi)).tail ++ [(layout v).mask]))) s := by
  have h := (layout_valid v).xorCode (fin4 i hi)
  have code := programText_slice (programLoaded_codeIn loaded)
    ((layout v).offset + (layout v).positions[i]) (v.xorBytes (fin4 i hi)) (by
      have bound := (layout_valid v).bound
      have pos : (layout v).positions[i] ≤ (layout v).positions[4] := by
        simpa only [Fin.getElem_fin] using (layout_valid v).positions ⟨i, by omega⟩
      have posnext : (layout v).positions[i + 1] ≤ (layout v).positions[4] := by
        simpa only [Fin.getElem_fin] using (layout_valid v).positions ⟨i + 1, by omega⟩
      have next := xor_length v i hi
      have hlen : (v.xorBytes (fin4 i hi)).length =
          3 + (v.am (fin4 i hi)).tail.length := by
        simp [Variant.xorBytes, Variant.am, fin4, Nat.add_comm]
        omega
      omega) h
  rw [address_eq v i (by omega)]
  simpa [Variant.xorBytes, Variant.am, fin4] using code

end Hkdf.Proofs.Common.Pad
