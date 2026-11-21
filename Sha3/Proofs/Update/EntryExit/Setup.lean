import Sha3.Proofs.Update.EntryExit.Push
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.MovzxLoad.Triple

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def setupChanges : List Component := [.reg 15, .reg 3, .reg 0, .rip]

theorem setupChanges_noMem : ∀ c ∈ setupChanges, ∀ a, ¬ c.Covers a := by
  simp [setupChanges, Component.Covers]

theorem setup_advance [Bindings] (v : Variant) {boundary : ReturnBoundary}
    (hb : ¬ InProgram boundary.rip) {s : RamState} (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = v.updateAddress + 11#64)
    (hm : MemReadable s (s.regValue .rdi) 1) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = partialAddress v ∧
      t.regValue .rbx = s.regValue .rdx ∧ t.regValue .r15 = s.regValue .rsi ∧
      t.regValue .rax = ((Operand.mem (s.regValue .rdi) : Operand 8).read s).setWidth 64 ∧
      AgreesExcept setupChanges s t := by
  have hsub1 : ∀ x ∈ codeRange (v.updateAddress + 11#64) [0x48, 0x89, 0xd3],
      x ∈ Extracted.programImage := by
    intro x hx
    exact prologueCode_subset v x (codeRange_mem_of_drop 11 (by decide +kernel) x hx)
  have hsub2 : ∀ x ∈ codeRange (v.updateAddress + 14#64) [0x49, 0x89, 0xf7],
      x ∈ Extracted.programImage := by
    intro x hx
    exact prologueCode_subset v x (codeRange_mem_of_drop 14 (by decide +kernel) x hx)
  let am : AddrMode := .base 7 .none
  have hsub3 : ∀ x ∈ codeRange (v.updateAddress + 17#64)
      (0x0f :: 0xb6 :: am.modrm 0 :: am.tail), x ∈ Extracted.programImage := by
    intro x hx
    exact prologueCode_subset v x (codeRange_mem_of_drop 17 (by decide +kernel) x hx)
  have hn (k : Nat) (hk : k < 20) : v.updateAddress + BitVec.ofNat 64 k ≠ boundary.rip :=
    fun he ↦ hb (he ▸ prologuePC_inProgram v hk)
  have hn20 : partialAddress v ≠ boundary.rip := by
    intro he
    apply hb
    rw [← he]
    cases v <;> exact ⟨0x48, imageSections_mem_toCodeMap_of_fetchByte (by decide +kernel)⟩
  have hstep1 := mov_r64_r64_effect_step (v.updateAddress + 11#64) 0x48 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ := hstep1.advances hr (hc.mono hsub1) hip (by
    simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using hn 14 (by decide))
  have hc1 := he1.codeIn (Effect.avoids_of_components_reg_rip
    (movR64R64Effect_components _ _ _ _) _) hc
  have ha1' : AgreesExcept setupChanges s t1 := he1.agrees.mono (by
    simp (config := { decide := true }) [movR64R64Effect_components, setupChanges])
  have hstep2 := mov_r64_r64_effect_step (v.updateAddress + 14#64) 0x49 0xf7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ := hstep2.advances hr1 (hc1.mono hsub2)
    (by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using he1.rip) (by
      simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using hn 17 (by decide))
  have hc2 := he2.codeIn (Effect.avoids_of_components_reg_rip
    (movR64R64Effect_components _ _ _ _) _) hc1
  have ha2' : AgreesExcept setupChanges t1 t2 := he2.agrees.mono (by
    simp (config := { decide := true }) [movR64R64Effect_components, setupChanges])
  have ha12 : AgreesExcept setupChanges s t2 := (ha1'.trans ha2').mono
    (fun c hc ↦ (List.mem_append.mp hc).elim id id)
  have hg7 : t2.regValue .rdi = s.regValue .rdi := ha12.read (n := 64) (r := 7) (by decide +kernel)
  have hex : t2.external = s.external := ha12.external setupChanges_noMem
  have hm2 : MemReadable t2 (am.addr t2 (v.updateAddress + 17#64 + 3#64)) 1 := by
    change MemReadable t2 (t2.regValue .rdi + 0#64) 1
    rw [BitVec.add_zero, hg7]
    exact hm.of_external_eq hex
  have hstep3 := movzx_r32_m8_effect_step (v.updateAddress + 17#64) 0 am
    (by unfold am AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ := hstep3.advances hr2 (hc2.mono hsub3) ⟨by
    simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using he2.rip, hm2⟩ (by
      simpa only [movzxR32M8Effect, am, AddrMode.tail, Disp.bytes, List.length_cons,
        List.length_nil, immBytes_length, Nat.reduceAdd, Nat.reduceDiv,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, partialAddress] using hn20)
  have ha3' : AgreesExcept setupChanges t2 t3 := he3.agrees.mono (by
    simp (config := { decide := true }) [movzxR32M8Effect_components, setupChanges])
  refine ⟨t3, (ha1.trans ha2).trans ha3, hr3,
    he3.codeIn (Effect.avoids_of_components_reg_rip (movzxR32M8Effect_components _ _ _ _ _) _) hc2,
    ?_, ?_, ?_, ?_, (ha12.trans ha3').mono (fun c hc ↦ (List.mem_append.mp hc).elim id id)⟩
  · simpa only [movzxR32M8Effect, am, AddrMode.tail, Disp.bytes, List.length_cons,
      List.length_nil, immBytes_length, Nat.reduceAdd, Nat.reduceDiv,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, partialAddress] using he3.rip
  · exact (he3.agrees.read (by simp only [movzxR32M8Effect_components]; decide +kernel)).trans
      ((he2.agrees.read (by simp only [movR64R64Effect_components]; decide +kernel)).trans
        he1.writes)
  · exact (he3.agrees.read (by simp only [movzxR32M8Effect_components]; decide +kernel)).trans
      (he2.writes.trans
        (he1.agrees.read (by simp only [movR64R64Effect_components]; decide +kernel)))
  · have hw := he3.writes
    change t3.regValue .rax =
      ((Operand.mem (t2.regValue .rdi + 0#64) : Operand 8).read t2).setWidth 64 at hw
    rw [BitVec.add_zero, hg7] at hw
    change t3.regValue .rax = (memLoad t2.external (s.regValue .rdi) 8).setWidth 64 at hw
    rw [hex] at hw
    exact hw

end Sha3.Proofs.Update
