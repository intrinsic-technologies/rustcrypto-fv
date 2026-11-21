import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Common.Field.SquareRoot.Exponent.Initialize.Store
import P256.Proofs.Common.Instructions.CrossPageStore.Mov

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Common.Field.SquareRoot.ExponentInitialize (external_of_store)

namespace P256.Proofs.Sec1.Affine.Compact.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def wordAt (s : RamState) (a v : BitVec 64) := (Operand.mem a : Operand 64).read s=v

theorem frame_store_r64 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1100d0 65 80 3360) (hf : Frame s t)
    (codeOffset offset : Nat) (disp : Disp) (rex : UInt8) (reg : BitVec 3)
    (hrex : RexWPrefix rex.toBitVec) (hx : rexX rex.toBitVec = 0) (hb : rexB rex.toBitVec = 0)
    (hdisp : disp.value = BitVec.ofNat 64 offset)
    (ho : offset + 8 ≤ 712)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hbound : codeOffset + (3 + (AddrMode.sib 4 none 0 disp).tail.length) < 118431)
    (hcode : Extracted.textBytes.toListFrom codeOffset (3 + (AddrMode.sib 4 none 0 disp).tail.length) =
      rex :: 0x89 :: (AddrMode.sib 4 none 0 disp).modrm reg :: (AddrMode.sib 4 none 0 disp).tail) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + (3 + (AddrMode.sib 4 none 0 disp).tail.length)) ∧
      wordAt u ((stackPtr s-760) + BitVec.ofNat 64 offset)
        ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read t) ∧
      AgreesExcept [.mem ((stackPtr s-760) + BitVec.ofNat 64 offset) 8, .rip] t u ∧
      u.external = memStore t.external ((stackPtr s-760) + BitVec.ofNat 64 offset)
        ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read t) := by
  let am := AddrMode.sib 4 none 0 disp
  let len := 3+am.tail.length
  change codeOffset + len < 118431 at hbound
  let ip := Extracted.textAddress + BitVec.ofNat 64 codeOffset
  have hsp : stackPtr t = (stackPtr s-760) := hf.rsp
  have haddr : storeAddrAt ip am len t = (stackPtr s-760) + BitVec.ofNat 64 offset := by
    change stackPtr t + disp.value = _
    rw [hsp, hdisp]
  have hw : P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      ((stackPtr s-760) + BitVec.ofNat 64 offset) 8 := by
    have h := ScalarFrame.stack_writable (frameOffset := 760) pre hf (offset := offset) (len := 8)
      (by decide) (by omega) (by decide)
    rwa [hsp] at h
  have ha : RangeApart ((stackPtr s-760) + BitVec.ofNat 64 offset) 8 ip len := by
    have h := ScalarFrame.stack_code (frameOffset := 760) pre hf (offset := offset) (len := 8)
      (codeOffset := codeOffset) (codeLen := len) (by decide) (by omega) (by omega)
    rwa [hsp] at h
  have hlen : (rex :: 0x89 :: am.modrm reg :: am.tail).length = len := by
    simp only [List.length_cons, len]
    omega
  have bytes := programText_slice (programLoaded_codeIn hf.loaded) codeOffset
    (rex :: 0x89 :: am.modrm reg :: am.tail) (by rw [hlen]; exact Nat.le_of_lt hbound)
    (by rw [hlen]; exact hcode)

  obtain ⟨u, run, ready, effect⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any ip rex hrex reg am
      (by simp [am, AddrMode.Valid, regLow]) hx hb).advances
      (readyToStep hf.machine hf.bindingsSupported) bytes ⟨hip, haddr ▸ hw, haddr ▸ ha⟩ (by
        have h := boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (codeOffset+len) hbound)
        simpa [movM64R64Effect, storeEffect, ip, BitVec.ofNat_add, BitVec.add_assoc, len, am] using h)
  have agrees : AgreesExcept [.mem ((stackPtr s-760) + BitVec.ofNat 64 offset) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components, haddr] at h
    exact h
  have value : wordAt u ((stackPtr s-760) + BitVec.ofNat 64 offset)
      ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read t) := by
    have h := effect.writes
    change wordAt u (storeAddrAt ip am len t) _ at h
    rwa [haddr] at h
  have frame : Frame s u := hf.after_effect (frameOffset := 760) pre (by decide) ready agrees (by
    intro c hc a hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨ScalarFrame.workRegion s 3360, by simp, ?_⟩
      have addr : (stackPtr s-760) + BitVec.ofNat 64 offset =
          stackPtr s - BitVec.ofNat 64 (760 - offset) := by
        have h := ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := offset) (t := t) hf.rsp (by decide) (by omega)
        rwa [hsp] at h
      rw [addr] at hv
      exact ScalarFrame.work_contains pre (by omega) (by omega) hv
    · exact hv.elim) (by simp)
  refine ⟨u, run, frame, ?_, value, agrees, external_of_store agrees hw.mem value⟩
  simpa [movM64R64Effect, storeEffect, ip, BitVec.ofNat_add, BitVec.add_assoc, len, am] using effect.rip

end P256.Proofs.Sec1.Affine.Compact.Compare
