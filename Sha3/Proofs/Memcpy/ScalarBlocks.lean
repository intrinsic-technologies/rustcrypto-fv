import Sha3.Proofs.Memcpy.Basic
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.Sub.Triple
import Sha3.Proofs.X86.Instructions.Shr.Triple
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple

namespace Sha3.Proofs.Memcpy

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def loopClobbers : List Component := [.reg 1, .reg 2, .flags, .rip]

private theorem loopStep [Bindings] {s : RamState} {pre : RamState → Prop}
    {e : RamState → Effect} {p : BitVec 64} {bs : List UInt8}
    (boundary : ReturnBoundary) (hstep : StepEffect pre (codeRange p bs) e)
    (hmem : (p, bs) ∈ instructionBytes) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (hp : pre s)
    (hsp : stackPtr s ≠ boundary.rsp)
    (hclobbers : ∀ q ∈ (e s).components, q ∈ loopClobbers) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (e s).Holds s t ∧
      AgreesExcept loopClobbers s t := by
  obtain ⟨t, hs, hr, hh⟩ := hstep s hready (instruction_codeIn hcode hmem) hp
  have hf := hh.agrees.mono hclobbers
  have htsp : stackPtr t = stackPtr s := hf.read (n := 64) (r := 4) (by decide)
  exact ⟨t, Advances.of_step hs (.inr (by change stackPtr t ≠ boundary.rsp; rw [htsp]; exact hsp)), hr,
    hf.codeIn (by simp [loopClobbers, Component.Covers]) hcode, hh, hf⟩

theorem prepare_steps_general [Bindings] {len lead : BitVec 64} (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x106a89)
    (hdx : (Operand.reg 2 : Operand 64).read s = len)
    (h8 : (Operand.reg 8 : Operand 64).read s = lead)
    (boundary : ReturnBoundary) (hsp : stackPtr s ≠ boundary.rsp) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x106a93 ∧ (Operand.reg 1 : Operand 64).read t = (len - lead) >>> 3 ∧ (Operand.reg 2 : Operand 64).read t = len - lead ∧
      AgreesExcept loopClobbers s t := by
  obtain ⟨a, hsa, ha, hca, ea, fa⟩ := loopStep boundary
    (show StepEffect (fun s => s.RIP = 0x106a89)
      (codeRange 0x106a89 [0x4c, 0x29, 0xc2]) (subR64R64Effect 0x106a89 2 8) from
        sub_r64_r64_effect_step 0x106a89 0x4c 0xc2 (by simp [RexWPrefix]) (by decide))
    (by decide +kernel) hr hc hip hsp (by simp [subR64R64Effect_components, loopClobbers])
  have adx : (Operand.reg 2 : Operand 64).read a = len - lead := by
    have he := ea.writes
    change (Operand.reg 2 : Operand 64).read a =
      (Operand.reg 2 : Operand 64).read s - (Operand.reg 8 : Operand 64).read s at he
    rw [hdx, h8] at he
    exact he
  have asp : stackPtr a = stackPtr s := fa.read (n := 64) (r := 4) (by decide)
  obtain ⟨b, hab, hb, hcb, eb, fb⟩ := loopStep boundary
    (show StepEffect (fun s => s.RIP = 0x106a8c)
      (codeRange 0x106a8c [0x48, 0x89, 0xd1]) (movR64R64Effect 0x106a8c 1 2) from
        mov_r64_r64_effect_step 0x106a8c 0x48 0xd1 (by simp [RexWPrefix]) (by decide))
    (by decide +kernel) ha hca ea.rip (asp ▸ hsp)
    (by simp [movR64R64Effect_components, loopClobbers])
  have bcx : (Operand.reg 1 : Operand 64).read b = len - lead := eb.writes.trans adx
  have bdx : (Operand.reg 2 : Operand 64).read b = len - lead :=
    (eb.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans adx
  have bsp : stackPtr b = stackPtr s :=
    (fb.read (n := 64) (r := 4) (by decide)).trans asp
  obtain ⟨t, hbt, ht, hct, et, ft⟩ := loopStep boundary
    (show StepEffect (fun s => s.RIP = 0x106a8f)
      (codeRange 0x106a8f [0x48, 0xc1, 0xe9, 0x03]) (shrR64Effect 0x106a8f 4 1 3) from
        shr_r64_imm8_effect_step 0x106a8f 0x48 0xe9 3
          (by simp [RexWPrefix]) (by decide) (by decide))
    (by decide +kernel) hb hcb eb.rip (bsp ▸ hsp)
    (by simp [shrR64Effect_components, loopClobbers])
  refine ⟨t, hsa.trans (hab.trans hbt), ht, hct, et.rip, ?_, ?_, ?_⟩
  · have he := et.writes
    change (Operand.reg 1 : Operand 64).read t = (Operand.reg 1 : Operand 64).read b >>> 3 at he
    rw [bcx] at he
    exact he
  · exact (et.agrees.read (n := 64) (r := 2)
      (by simp [shrR64Effect_components])).trans bdx
  · exact (fa.trans (fb.trans ft)).mono (by
      intro q hq
      simpa only [List.mem_append, or_self] using hq)

theorem remainder_steps_general [Bindings] {len : BitVec 64} (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x106a96)
    (hdx : (Operand.reg 2 : Operand 64).read s = len)
    (boundary : ReturnBoundary) (hsp : stackPtr s ≠ boundary.rsp) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x106a9c ∧ (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (len.toNat % 8) ∧ AgreesExcept loopClobbers s t := by
  obtain ⟨a, hsa, ha, hca, ea, fa⟩ := loopStep boundary
    (show StepEffect (fun s => s.RIP = 0x106a96)
      (codeRange 0x106a96 [0x83, 0xe2, 0x07]) (andR32Imm8Effect 0x106a96 3 2 7) from
        and_r32_imm8_effect_step 0x106a96 0xe2 7 (by decide) (by decide))
    (by decide +kernel) hr hc hip hsp
    (by simp [andR32Imm8Effect_components, loopClobbers])
  have adx : (Operand.reg 2 : Operand 64).read a = BitVec.ofNat 64 (len.toNat % 8) := by
    have he := ea.writes
    change (Operand.reg 2 : Operand 64).read a =
      (((Operand.reg 2 : Operand 32).read s &&& 7#32).setWidth 64) at he
    have hsmall : (Operand.reg 2 : Operand 32).read s = len.setWidth 32 := by
      change ((Operand.reg 2 : Operand 64).read s).setWidth 32 = len.setWidth 32
      rw [hdx]
    rw [hsmall] at he
    rw [he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    change (len.toNat % 2^32 &&& (2^3-1)) % 2^64 = len.toNat % 8 % 2^64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    congr 1
    exact Nat.mod_mod_of_dvd _ (by decide)
  have asp : stackPtr a = stackPtr s := fa.read (n := 64) (r := 4) (by decide)
  obtain ⟨t, hat, ht, hct, et, ft⟩ := loopStep boundary
    (show StepEffect (fun s => s.RIP = 0x106a99)
      (codeRange 0x106a99 [0x48, 0x89, 0xd1]) (movR64R64Effect 0x106a99 1 2) from
        mov_r64_r64_effect_step 0x106a99 0x48 0xd1 (by simp [RexWPrefix]) (by decide))
    (by decide +kernel) ha hca ea.rip (asp ▸ hsp)
    (by simp [movR64R64Effect_components, loopClobbers])
  exact ⟨t, hsa.trans hat, ht, hct, et.rip, et.writes.trans adx,
    (fa.trans ft).mono (by intro q hq; simpa only [List.mem_append, or_self] using hq)⟩

theorem prepare_steps [Bindings] (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x106a89)
    (hdx : (Operand.reg 2 : Operand 64).read s = 208)
    (h8 : (Operand.reg 8 : Operand 64).read s = 0)
    (boundary : ReturnBoundary) (hsp : stackPtr s ≠ boundary.rsp) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x106a93 ∧ (Operand.reg 1 : Operand 64).read t = 26 ∧
      (Operand.reg 2 : Operand 64).read t = 208 ∧ AgreesExcept loopClobbers s t :=
  prepare_steps_general s hr hc hip hdx h8 boundary hsp

theorem remainder_steps [Bindings] (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x106a96)
    (hdx : (Operand.reg 2 : Operand 64).read s = 208)
    (boundary : ReturnBoundary) (hsp : stackPtr s ≠ boundary.rsp) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x106a9c ∧ (Operand.reg 1 : Operand 64).read t = 0 ∧
      AgreesExcept loopClobbers s t :=
  remainder_steps_general s hr hc hip hdx boundary hsp

end Sha3.Proofs.Memcpy
