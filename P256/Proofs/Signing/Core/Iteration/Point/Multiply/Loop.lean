import P256.Proofs.Signing.Core.Iteration.Point.Call
import P256.Proofs.Projective.Multiply.Machine.Loop.Correct
import P256.Proofs.PublicPoint.Value

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply Projective.Multiply.Machine
open NextNonce (scalarFrame base_add)

def loopSite : Loop.CallSite 0x103250 :=
  ⟨0xcf6a,0xffff62e1,by decide,by decide +kernel,by decide +kernel⟩

theorem loop_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cf6a)
    (source : t.regValue .rsi = frameBase s+1328)
    (destination : t.regValue .rdi = frameBase s+176)
    (digits : t.regValue .rcx = frameBase s+432)
    (tableCount : t.regValue .rdx = 1) (digitCount : t.regValue .r8 = 1)
    (input : Lookup.TableAt t (frameBase s+1328) (Projective.table Basepoint.basePoint))
    (digitBytes : Bytes t.external (frameBase s+432) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte nonce i))) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10cf6f ∧
      ProjectiveAt u (frameBase s+176) (model Basepoint.basePoint nonce) ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) ∧
      (∀ offset len, offset+len ≤ 2280 → (offset+len ≤ 176 ∨ 272 ≤ offset) →
        ∀ i < len, u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) := by
  obtain ⟨v,run,ready,effect⟩ := call_site pre frame loopSite
    (inProgram_of_textOffset 0x3250 (by decide)) rip
  have cp : CalleePre v boundary 0x103250 768 96 1400 :=
    local_call_pre pre frame ready effect (inProgram_of_textOffset 0xcf6f (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
      source destination
  have srcV : v.regValue .rsi = frameBase s+1328 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dstV : v.regValue .rdi = frameBase s+176 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have digV : v.regValue .rcx = frameBase s+432 :=
    (effect.agrees.read (n := 64) (r := 1) (by simp)).trans digits
  have called := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  let layout : StackCallLayout 4584 65 96 1400 :=
    ⟨2288,1848,2104,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have dp := CalleePre.of_stack pre.toCalleePre layout called.bindingsSupported called.machine
    called.directionFlag called.loaded called.allocated effect.rip called.rsp
    (digV.trans (base_add s (offset := 432) (by decide)))
    (dstV.trans (base_add s (offset := 176) (by decide))) (Loop.call_return_program loopSite effect)
  have lp : Loop.Pre v boundary := ⟨cp,
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans tableCount,
    (effect.agrees.read (n := 64) (r := 8) (by simp)).trans digitCount,
    dp.inputBounded,dp.inputAllocated,dp.separation 0 1 (by decide),dp.separation 0 2 (by decide)⟩
  have inputV : Lookup.TableAt v (v.regValue .rsi) (Projective.table Basepoint.basePoint) := by
    rw [srcV]
    intro index
    apply (input index).of_bytes_eq
    intro i hi
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact local_call_copy frame effect (offset := 1328) (len := 768) (by decide)
      _ (by have := index.isLt; omega)
  have bytesV : Bytes v.external (v.regValue .rcx) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte nonce i)) := by
    rw [digV]
    intro i hi
    exact (local_call_copy frame effect (by decide) i hi).trans (digitBytes i hi)
  obtain ⟨u,result,value⟩ := Loop.loop_correct lp inputV
  rw [Loop.linearCombination_eq_model bytesV,dstV] at value
  obtain ⟨fuel,executed⟩ := result.execution
  exact ⟨1+fuel,u,run.trans executed,after_call pre frame ready effect result (by decide)
      (by decide) destination,result.rip.trans (callEffect_stack effect).1,value,
    call_registers effect result,
    fun offset len bound apart => local_result_copy pre frame effect result destination bound (by decide) apart⟩

end P256.Proofs.Signing.Core.Iteration.Point.Multiply
