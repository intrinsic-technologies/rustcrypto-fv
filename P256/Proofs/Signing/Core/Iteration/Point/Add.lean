import P256.Proofs.Signing.Core.Iteration.Point.Call
import P256.Proofs.Signing.Core.Iteration.Point.Constants
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Projective.Add
import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Loop
open Projective.Multiply.Machine.Basepoint.TableSteps
open NextNonce (scalarFrame base_add)

theorem add_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective} {sourceOffset : Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = frameBase s+1328)
    (src : t.regValue .rsi = frameBase s+BitVec.ofNat 64 sourceOffset)
    (bound : sourceOffset+96 ≤ 1328)
    (leftAt : ProjectiveAt t (frameBase s+1328) left)
    (rightAt : ProjectiveAt t (frameBase s+BitVec.ofNat 64 sourceOffset) right) :
    ∃ u, PointCallResult s t u boundary site.returnRip 952 (left.add right) 65 4584 2280 := by
  obtain ⟨v,run,ready,effect⟩ := call_site pre frame site (inProgram_of_textOffset 0x51f0 (by decide)) rip
  have cp := local_call_pre pre frame ready effect
    (inputBytes := 96) (outputBytes := 96) (reserve := 920)
    (by simpa only [CallSite.returnRip,BitVec.ofNat_add,BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat] using inProgram_of_textOffset (site.offset+5) site.bounded)
    (by decide) (by omega) (by decide) (by omega) (by decide) (.inl bound) src dst
  have srcV : v.regValue .rsi = frameBase s+BitVec.ofNat 64 sourceOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have dstV : v.regValue .rdi = frameBase s+1328 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    exact leftAt.of_bytes_eq (local_call_copy frame effect (by decide))
  have rightV : ProjectiveAt v (v.regValue .rsi) right := by
    rw [srcV]
    exact rightAt.of_bytes_eq (local_call_copy frame effect (by omega))
  obtain ⟨u,result,value⟩ := Projective.projective_add_correct cp leftV rightV
  have output : v.regValue .rdi = stackPtr s-952 :=
    dstV.trans (base_add s (offset := 1328) (by decide))
  exact ⟨u,finish_call pre.toCalleePre (scalarFrame frame) run ready effect output
    (by decide) (by decide) (by decide) result value⟩

theorem add_generator [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left : Projective}
    (pre : SignPre s boundary) (frame : Frame s t) (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = frameBase s+1328) (src : t.regValue .rsi = 0x202ac8)
    (leftAt : ProjectiveAt t (frameBase s+1328) left) :
    ∃ u, PointCallResult s t u boundary site.returnRip 952
      (left.add Projective.Multiply.Machine.Basepoint.basePoint) 65 4584 2280 := by
  obtain ⟨v,run,ready,effect⟩ := call_site pre frame site (inProgram_of_textOffset 0x51f0 (by decide)) rip
  have stateV := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  have srcV : v.regValue .rsi = 0x202ac8 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have dstV : v.regValue .rdi = stackPtr s-952 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst).trans
      (base_add s (offset := 1328) (by decide))
  have region : registerRegion v .rsi 96 = MemoryRegion.mk 0x202ac8 96 := by
    simp only [registerRegion,srcV]
    rfl
  have bounded : (registerRegion v .rsi 96).Bounded := by
    rw [region]
    change 0x202ac8+96 < 2^32
    decide
  have allocated : (registerRegion v .rsi 96).Allocated v.external := by
    rw [region]
    intro a ha
    obtain ⟨b,hb⟩ := generator_region_inProgram ha
    exact ⟨b,stateV.loaded a b hb⟩
  have disjoint : (registerRegion v .rsi 96).Disjoint (Stack.region s 4584) := by
    rw [region]
    intro a ha hs
    have small : a < 2^64 := by
      change 0x202ac8 ≤ a ∧ a < 0x202ac8+96 at ha
      omega
    have eq : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt small
    exact pre.avoids (Stack.region s 4584) (by simp) (BitVec.ofNat 64 a)
      (eq.symm ▸ hs) (.inl (generator_region_inProgram (eq.symm ▸ ha)))
  let layout : StackBufferLayout 4584 96 920 :=
    ⟨2288,952,by decide,by decide,by decide,by decide⟩
  have cp := CalleePre.of_disjoint_input_and_stack layout pre.stack
    (pre.avoids _ (by simp)) stateV.bindingsSupported stateV.machine stateV.directionFlag
    stateV.loaded effect.rip stateV.rsp bounded allocated disjoint dstV stateV.allocated
    pre.outerBoundary (call_return_program site effect)
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    have address : frameBase s+1328 = stackPtr s-952 := base_add s (offset := 1328) (by decide)
    rw [← address]
    exact leftAt.of_bytes_eq (local_call_copy frame effect (by decide))
  have rightV : ProjectiveAt v (v.regValue .rsi) Projective.Multiply.Machine.Basepoint.basePoint := by
    rw [srcV]
    exact generator_at stateV.loaded
  obtain ⟨u,result,value⟩ := Projective.projective_add_correct cp leftV rightV
  exact ⟨u,finish_call pre.toCalleePre (scalarFrame frame) run ready effect dstV
    (by decide) (by decide) (by decide) result value⟩

end P256.Proofs.Signing.Core.Iteration.Point
