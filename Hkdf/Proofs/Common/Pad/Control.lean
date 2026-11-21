import Hkdf.Proofs.Common.Pad.Byte
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions.CrossPageStore

theorem entry_eq (v : Variant) :
    v.entry = Hkdf.Spec.Program.Extracted.textAddress +
      BitVec.ofNat 64 (layout v).offset := by
  simp [Variant.entry, Variant.pc, (layout_valid v).initial]

theorem add_code {s : RamState} (loaded : ProgramLoaded s) (v : Variant) :
    CodeIn (codeRange (address v 4) [0x48, 0x83, 0xc0, 4]) s := by
  have h := (layout_valid v).addCode
  have code := programText_slice (programLoaded_codeIn loaded)
    ((layout v).offset + (layout v).positions[4]) [0x48, 0x83, 0xc0, 4] (by
      have bound := (layout_valid v).bound
      have hlen : [0x48, 0x83, 0xc0, 4].length = 4 := by rfl
      omega) h
  rw [address_eq v 4 (by decide)]
  exact code

theorem cmp_code_of_layout {s : RamState} (loaded : ProgramLoaded s) (v : Variant) :
    CodeIn (codeRange (address v 4 + 4) [0x48, 0x83, 0xf8, UInt8.ofNat ((layout v).first + 64)]) s := by
  have h := (layout_valid v).cmpCode
  have code := programText_slice (programLoaded_codeIn loaded)
    ((layout v).offset + (layout v).positions[4] + 4)
    [0x48, 0x83, 0xf8, UInt8.ofNat ((layout v).first + 64)] (by
      have bound := (layout_valid v).bound
      have hlen : [0x48, 0x83, 0xf8, UInt8.ofNat ((layout v).first + 64)].length = 4 := by rfl
      omega) h
  rw [address_eq v 4 (by decide)]
  rw [BitVec.add_assoc]
  change CodeIn (codeRange
    (Hkdf.Spec.Program.Extracted.textAddress +
      (BitVec.ofNat 64 ((layout v).offset + (layout v).positions[4]) +
        BitVec.ofNat 64 4)) [0x48, 0x83, 0xf8, UInt8.ofNat ((layout v).first + 64)]) s
  rw [← BitVec.ofNat_add]
  exact code

theorem cmp_code {s : RamState} (loaded : ProgramLoaded s) (v : Variant)
    (first : (layout v).first = 3) :
    CodeIn (codeRange (address v 4 + 4) [0x48, 0x83, 0xf8, 0x43]) s := by
  simpa [first] using cmp_code_of_layout loaded v

theorem branch_code {s : RamState} (loaded : ProgramLoaded s) (v : Variant) :
    CodeIn (codeRange (address v 4 + 8)
      [0x75, UInt8.ofBitVec (layout v).branchDisp]) s := by
  have h := (layout_valid v).branchCode
  have code := programText_slice (programLoaded_codeIn loaded)
    ((layout v).offset + (layout v).positions[4] + 8)
    [0x75, UInt8.ofBitVec (layout v).branchDisp] (by
      have bound := (layout_valid v).bound
      have hlen : [0x75, UInt8.ofBitVec (layout v).branchDisp].length = 2 := by rfl
      omega) (by simpa using h)
  rw [address_eq v 4 (by decide)]
  rw [BitVec.add_assoc]
  change CodeIn (codeRange
    (Hkdf.Spec.Program.Extracted.textAddress +
      (BitVec.ofNat 64 ((layout v).offset + (layout v).positions[4]) +
        BitVec.ofNat 64 8)) [0x75, UInt8.ofBitVec (layout v).branchDisp]) s
  rw [← BitVec.ofNat_add]
  exact code

theorem branch_target (v : Variant) :
    branchTarget v.branchPC 2 ((layout v).branchDisp.signExtend 64) = v.entry :=
  (layout_valid v).branch

theorem branch_end (v : Variant) :
    address v 4 + 8 + 2 = v.exit := by
  change v.addPC + 8 + 2 = v.addPC + 10
  simp [BitVec.add_assoc, BitVec.reduceAdd]

theorem address_add_offset (v : Variant) (offset : Nat) :
    address v 4 + BitVec.ofNat 64 offset =
      v.entry + BitVec.ofNat 64 ((layout v).positions[4] + offset) := by
  rw [address_eq v 4 (by decide), entry_eq v, BitVec.add_assoc, ← BitVec.ofNat_add,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  simp only [Nat.add_assoc]

theorem address_inProgram (v : Variant) (offset : Nat)
    (bound : offset ≤ (layout v).positions[4] + 10) :
    InProgram (v.entry + BitVec.ofNat 64 offset) := by
  have h := inProgram_of_textOffset ((layout v).offset + offset) (by
    have bound' := (layout_valid v).bound
    omega)
  have addr : v.entry + BitVec.ofNat 64 offset =
      Hkdf.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 ((layout v).offset + offset) := by
    rw [entry_eq v, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [addr]
  exact h

theorem advance_of_layout [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    {n : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = address v 4)
    (counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + (layout v).first)) (hn : n < 16) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if n + 1 < 16 then v.entry else v.exit) ∧
      t.regValue .rax = BitVec.ofNat 64 (4 * (n + 1) + (layout v).first) ∧
      AgreesExcept [.reg 0, .flags, .rip] s t := by
  have progAdd : InProgram (address v 4 + BitVec.ofNat 64 4) := by
    rw [address_add_offset v 4]
    exact address_inProgram v ((layout v).positions[4] + 4) (by
      have bound := (layout_valid v).bound
      omega)
  have progCmp : InProgram (address v 4 + BitVec.ofNat 64 8) := by
    rw [address_add_offset v 8]
    exact address_inProgram v ((layout v).positions[4] + 8) (by
      have bound := (layout_valid v).bound
      omega)
  obtain ⟨u, run1, readyU, add⟩ :=
    (add_r64_imm8_effect_step (address v 4) 0x48 0xc0 4
      (by simp [RexWPrefix]) rfl rfl).advances ready (add_code loaded v) rip
      (by simpa [addR64Imm8Effect] using boundary_ne_program outside progAdd)
  change (addR64Imm8Effect (address v 4) 0 4 s).Holds s u at add
  have memU : u.external = s.external := add.agrees.external (by simp [Component.Covers])
  have loadedU : ProgramLoaded u := by intro a b h; rw [memU]; exact loaded a b h
  have counterU : u.regValue .rax = BitVec.ofNat 64 (4 * (n + 1) + (layout v).first) := by
    have h : u.regValue .rax = s.regValue .rax + 4 := add.writes
    rw [h, counter]
    change BitVec.ofNat 64 (4 * n + (layout v).first) + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  obtain ⟨v', run2, readyV, compare⟩ :=
    (cmp_r64_imm8_effect_step (address v 4 + 4) 0x48 0xf8 v.limit
      (by simp [RexWPrefix]) rfl rfl).advances readyU (by
        simpa only [Variant.limit, immBytes, immByte, Nat.reduceDiv,
          show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
          Nat.mul_zero, BitVec.extractLsb'_eq_self, UInt8.ofNat] using
          (cmp_code_of_layout loadedU v)) add.rip
        (by simpa only [cmpR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd] using
          boundary_ne_program outside progCmp)
  change (cmpR64Imm8Effect (address v 4 + 4) 0 v.limit u).Holds u v' at compare
  have memV : v'.external = u.external := compare.agrees.external (by simp [Component.Covers])
  have loadedV : ProgramLoaded v' := by intro a b h; rw [memV]; exact loadedU a b h
  have limit : v.limit.signExtend 64 = BitVec.ofNat 64 ((layout v).first + 64) := by
    have bound := (layout_valid v).first
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (x := v.limit) (by
      apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
      simp only [Variant.limit, BitVec.toNat_ofNat]
      change 2 * (((layout v).first + 64) % 256) < 256
      omega)]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide : 8 ≤ 64) (by omega)
  have flag : (StatusFlags.ofRFLAGS v'.RFLAGS).ZF = decide (n + 1 = 16) := by
    have h : (StatusFlags.ofRFLAGS v'.RFLAGS).ZF = (u.regValue .rax - v.limit.signExtend 64 == 0) :=
      compare.flags.2.2.2.1
    rw [h, counterU, limit]
    by_cases eq : n + 1 = 16
    · simp only [eq, Nat.reduceMul, Nat.add_comm 64, BitVec.sub_self]
      decide
    · have ne : BitVec.ofNat 64 (4 * (n + 1) + (layout v).first) -
          BitVec.ofNat 64 ((layout v).first + 64) ≠ 0#64 := by
        intro h
        have he := congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 ((layout v).first + 64)) h
        rw [BitVec.sub_add_cancel, BitVec.zero_add] at he
        have ht := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at ht
        have bound := (layout_valid v).first
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
        omega
      simp [ne, eq]
  have target :
      (jccEffect (address v 4 + 8) 2 5 ((layout v).branchDisp.signExtend 64) v').rip =
        (if n + 1 < 16 then v.entry else v.exit) := by
    simp only [jccEffect, branchEffect, condHolds, flag]
    by_cases lt : n + 1 < 16
    · have ne : ¬ n + 1 = 16 := by omega
      simp only [ne, decide_false, Bool.not_false, reduceIte, lt, branchTarget]
      exact branch_target v
    · have eq : n + 1 = 16 := by omega
      simp only [eq, decide_true, Bool.not_true]
      exact branch_end v
  have branchCode : CodeIn (codeRange (address v 4 + 8)
      (jccOpcode8 5 :: immBytes 8 (layout v).branchDisp)) v' := by
    simpa [jccOpcode8, immBytes, immByte] using branch_code loadedV v
  obtain ⟨t, run3, readyT, branch⟩ :=
    (jcc_rel8_effect_step (address v 4 + 8) 5 (layout v).branchDisp).advances readyV
      branchCode
      ⟨(by
          have hrip : v'.RIP = address v 4 + BitVec.ofNat 64 8 := by
            simpa only [cmpR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd] using compare.rip
          exact hrip),
        (by intro h; cases v <;> decide +kernel)⟩
      (by rw [target]
          have progExit : InProgram v.exit := by
            rw [← branch_end v]
            have h := address_inProgram v ((layout v).positions[4] + 10) (by
              have bound := (layout_valid v).bound
              omega)
            rw [← address_add_offset v 10] at h
            simpa [BitVec.add_assoc, BitVec.reduceAdd] using h
          split
          · exact boundary_ne_program outside (by simpa using address_inProgram v 0 (by omega))
          · exact boundary_ne_program outside progExit)
  have frame : AgreesExcept [.reg 0, .flags, .rip] s t :=
    ((add.agrees.trans compare.agrees).trans branch.agrees).mono
      (by simp [jccEffect, branchEffect, Effect.components, addR64Imm8Effect,
        cmpR64Imm8Effect, Write.component, Operand.component])
  refine ⟨t, (run1.trans run2).trans run3, readyT, ?_, branch.rip.trans target, ?_, frame⟩
  · intro a b h
    rw [frame.external (by simp [Component.Covers])]
    exact loaded a b h
  · exact (branch.agrees.read (n := 64) (r := 0) (by simp [jccEffect])).trans
      ((compare.agrees.read (n := 64) (r := 0) (by simp)).trans counterU)

theorem advance [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    {n : Nat} (first : (layout v).first = 3)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = address v 4)
    (counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + (layout v).first)) (hn : n < 16) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if n + 1 < 16 then v.entry else v.exit) ∧
      t.regValue .rax = BitVec.ofNat 64 (4 * (n + 1) + (layout v).first) ∧
      AgreesExcept [.reg 0, .flags, .rip] s t := by
  have _ := first
  exact advance_of_layout ready loaded outside rip counter hn

end Hkdf.Proofs.Common.Pad
