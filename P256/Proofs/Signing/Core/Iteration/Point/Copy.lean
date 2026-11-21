import P256.Proofs.Signing.Core.Iteration.Point.Constants
import P256.Proofs.Signing.Core.Iteration.Point.State
import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Basepoint.TableSteps
open NextNonce (scalarFrame coreFrame base_add)

def copyComponents (s : RamState) (offset : Nat) : List Component :=
  [.reg 6,.reg 7,.reg 1,.mem (frameBase s + BitVec.ofNat 64 offset) 96,.rip]

theorem copy_generator [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t)
    (codeOffset : Nat) (codeBound : codeOffset+3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3,0x48,0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (offset : Nat) (bound : offset+96 ≤ 2232)
    (dst : t.regValue .rdi = frameBase s + BitVec.ofNat 64 offset)
    (count : t.regValue .rcx = 12) (src : t.regValue .rsi = 0x202ac8) :
    ∃ u, Advances boundary 12 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      ProjectiveAt u (frameBase s + BitVec.ofNat 64 offset)
        Projective.Multiply.Machine.Basepoint.basePoint ∧
      AgreesExcept (copyComponents s offset) t u := by
  have dst' := dst.trans (base_add s (by omega))
  obtain ⟨u,run,state,ripU,value,agrees,_⟩ := copy_to_stack (frameOffset := 2280) (frameBound := by decide) pre.toCalleePre (scalarFrame frame)
    codeOffset codeBound codeBytes rip (2280-offset) (by omega) (by omega) dst' count
    (by rw [src]; exact generator_readable frame.loaded)
    (by rw [src,dst']; exact generator_stack_disjoint pre.toCalleePre (by omega) (by omega))
    (by rw [src]; exact generator_at frame.loaded)
  refine ⟨u,run,coreFrame state,ripU,?_,?_⟩
  · rwa [← base_add s (offset := offset) (by omega)] at value
  · simpa only [copyComponents,Projective.Multiply.Machine.Basepoint.TableSteps.copyComponents,
      ← base_add s (offset := offset) (by omega)] using agrees

theorem copy_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {sourceOffset : Nat}
    (pre : SignPre s boundary) (frame : Frame s t)
    (codeOffset : Nat) (codeBound : codeOffset+3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3,0x48,0xa5])
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 codeOffset)
    (offset : Nat) (bound : offset+96 ≤ 2136)
    (dst : t.regValue .rdi = frameBase s+BitVec.ofNat 64 offset)
    (count : t.regValue .rcx = 12) (sourceBound : sourceOffset+96 ≤ 2280)
    (apart : offset+96 ≤ sourceOffset ∨ sourceOffset+96 ≤ offset)
    (src : t.regValue .rsi = frameBase s+BitVec.ofNat 64 sourceOffset)
    (input : ProjectiveAt t (frameBase s+BitVec.ofNat 64 sourceOffset) point) :
    ∃ u, Advances boundary 12 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress+BitVec.ofNat 64 codeOffset+(3 : BitVec 64) ∧
      ProjectiveAt u (frameBase s+BitVec.ofNat 64 offset) point ∧
      AgreesExcept (copyComponents s offset) t u := by
  have dst' := dst.trans (base_add s (by omega))
  have src' := src.trans (base_add s (by omega))
  obtain ⟨u,run,state,ripU,value,agrees,_⟩ :=
    Projective.Multiply.Machine.Basepoint.TableSteps.copy_stack
      (frameOffset := 2280) (frameBound := by decide) pre.toCalleePre (scalarFrame frame)
      codeOffset codeBound codeBytes rip (2280-offset) (by omega) (by omega)
      dst' count (by omega) (by omega) (by omega) src'
      (by rwa [← base_add s (offset := sourceOffset) (by omega)])
  refine ⟨u,run,coreFrame state,ripU,?_,?_⟩
  · rwa [← base_add s (offset := offset) (by omega)] at value
  · simpa only [copyComponents,Projective.Multiply.Machine.Basepoint.TableSteps.copyComponents,
      ← base_add s (offset := offset) (by omega)] using agrees

theorem copy_byte {s t u : RamState} {offset i : Nat}
    (agrees : AgreesExcept (copyComponents s offset) t u)
    (bound : offset+96 ≤ 2232) (small : i < 2^64)
    (apart : i < offset ∨ offset+96 ≤ i) :
    u.external[frameBase s+BitVec.ofNat 64 i]? =
      t.external[frameBase s+BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  simp only [copyComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  obtain ⟨j,hj,eq⟩ := ha
  rw [BitVec.add_assoc,← BitVec.ofNat_add] at eq
  have h := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase s)).mp eq)
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (by omega : offset+j < 2^64)] at h
  omega

theorem copy_preserved {s t u : RamState} {offset : Nat}
    (agrees : AgreesExcept (copyComponents s offset) t u)
    (bound : offset+96 ≤ 2232)
    (apart : ∀ i, LiveOffset i → i < offset ∨ offset+96 ≤ i) : Preserved s t u := by
  intro i live
  exact copy_byte agrees bound (by rcases live with h|h|h|h <;> omega) (apart i live)

theorem copy_point {s t u : RamState} {offset source : Nat} {point : Projective}
    (agrees : AgreesExcept (copyComponents s offset) t u)
    (bound : offset+96 ≤ 2232) (sourceBound : source+96 ≤ 2232)
    (apart : source+96 ≤ offset ∨ offset+96 ≤ source)
    (value : ProjectiveAt t (frameBase s+BitVec.ofNat 64 source) point) :
    ProjectiveAt u (frameBase s+BitVec.ofNat 64 source) point := by
  apply value.of_bytes_eq
  intro i hi
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
    copy_byte agrees bound (i := source+i) (by omega) (by omega)

end P256.Proofs.Signing.Core.Iteration.Point
