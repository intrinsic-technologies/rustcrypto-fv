import Sha1.Proofs.Buffered.Update.Slices.Copy
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (program_text_slice)
open Sha1.Proofs.Buffered.Finalize (pageApart_of_avoids rangeApart_text text_address_ne_return)

private theorem counter_pre {s : RamState} {offset : Nat}
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 0x118) 8)
    (hip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (hbytes : offset + 8 ≤ Extracted.textBytes.size) :
    RmwPre (Extracted.textAddress + BitVec.ofNat 64 offset) (.sib 4 none 0 (.d32 0x118)) 8 8 s :=
  ⟨hip, ⟨hw.readable.low, hw.readable.mem,
    pageApart_of_avoids (by decide) hw.readable.low hw.tables⟩, rangeApart_text hw.code hbytes⟩

private theorem counter_code {s t : RamState}
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 0x118) 8)
    (hc : CodeIn Extracted.programImage s)
    (ha : AgreesExcept [.mem (stackPtr s + 0x118) 8, .flags, .rip] s t) :
    CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept ha _ hc
  intro x hx c hm hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · obtain ⟨i, hi, he⟩ := hcov
    exact hw.code i hi (he ▸ ⟨x.2, hx⟩)
  · exact hcov.elim
  · exact hcov.elim

theorem add_counter [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x101d65)
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 0x118) 8) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101d6d ∧ AgreesExcept [.mem (stackPtr s + 0x118) 8, .flags, .rip] s t ∧
      (Operand.mem (stackPtr s + 0x118) : Operand 64).read t =
        (Operand.mem (stackPtr s + 0x118) : Operand 64).read s +
          (Operand.reg 2 : Operand 64).read s := by
  let am : AddrMode := .sib 4 none 0 (.d32 0x118)
  have had : am.addr s (0x101d65 + BitVec.ofNat 64 8) = stackPtr s + 0x118 := rfl
  have hb : CodeIn (codeRange 0x101d65 (0x48 :: 0x01 :: am.modrm 2 :: am.tail)) s := by
    rw [show 0x48 :: 0x01 :: am.modrm 2 :: am.tail = [0x48, 0x01, 0x94, 0x24, 0x18, 1, 0, 0] by decide +kernel]
    exact program_text_slice hc 0x1d65 8 (by decide +kernel)
  have hp := counter_pre (offset := 0x1d65) hw hip (by decide +kernel)
  obtain ⟨t, ha, ht, he⟩ := (add_m64_r64_effect_step 0x101d65 0x48
    (by decide) 2 am (by decide) (by decide) (by decide)).advances hr hb hp
    (text_address_ne_return hout 0x1d6d (by decide +kernel))
  have hComponents :
      (addMREffect 0x101d65 8 64 2 am s).components =
        [.mem (stackPtr s + 0x118) 8, .flags, .rip] := by
    rw [addMREffect_components, had]
  have hag : AgreesExcept [.mem (stackPtr s + 0x118) 8, .flags, .rip] s t := by
    rw [← hComponents]
    exact he.agrees
  exact ⟨t, ha, ht, counter_code hw hc hag, he.rip, hag, he.writes⟩

theorem inc_counter [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x101d2f)
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 0x118) 8) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101d37 ∧ AgreesExcept [.mem (stackPtr s + 0x118) 8, .flags, .rip] s t ∧
      (Operand.mem (stackPtr s + 0x118) : Operand 64).read t =
        (Operand.mem (stackPtr s + 0x118) : Operand 64).read s + 1 := by
  let am : AddrMode := .sib 4 none 0 (.d32 0x118)
  have had : am.addr s (0x101d2f + BitVec.ofNat 64 8) = stackPtr s + 0x118 := rfl
  have hb : CodeIn (codeRange 0x101d2f (0x48 :: 0xff :: am.modrm 0 :: am.tail)) s := by
    rw [show 0x48 :: 0xff :: am.modrm 0 :: am.tail = [0x48, 0xff, 0x84, 0x24, 0x18, 1, 0, 0] by decide +kernel]
    exact program_text_slice hc 0x1d2f 8 (by decide +kernel)
  have hp := counter_pre (offset := 0x1d2f) hw hip (by decide +kernel)
  obtain ⟨t, ha, ht, he⟩ := (inc_m64_effect_step 0x101d2f 0x48
    (by decide) am (by decide) (by decide) (by decide)).advances hr hb hp
    (text_address_ne_return hout 0x1d37 (by decide +kernel))
  have hComponents :
      (incMEffect 0x101d2f 8 64 am s).components =
        [.mem (stackPtr s + 0x118) 8, .flags, .rip] := by
    rw [incMEffect_components, had]
  have hag : AgreesExcept [.mem (stackPtr s + 0x118) 8, .flags, .rip] s t := by
    rw [← hComponents]
    exact he.agrees
  exact ⟨t, ha, ht, counter_code hw hc hag, he.rip, hag, he.writes⟩

end Sha1.Proofs.Buffered.Update.Slices
