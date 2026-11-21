import P256.Proofs.Ecdh.Interface
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Registers
import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Copy
import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Projective.Add
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open Projective.Multiply.Machine.Loop

export Projective.Multiply.Machine.Basepoint (register_block)
export Projective.Multiply.Machine.Basepoint.TableSteps (copyComponents copy_stack copy_byte)

abbrev PointCallResult [Bindings] (s t u : RamState) (boundary : ReturnBoundary)
    (ret : BitVec 64) (outputOffset : Nat) (point : Projective) : Prop :=
  Projective.Multiply.Machine.Basepoint.TableSteps.PointCallResult
    s t u boundary ret outputOffset point 32 3464 2056

theorem copy_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {destination offset : Nat} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (agrees : AgreesExcept (copyComponents s destination) t u)
    (destBound : destination ≤ 3464) (destSaved : 144 ≤ destination)
    (ho : offset ≤ 3464) (hl : 96 ≤ offset + 8)
    (apart : offset + 96 ≤ destination ∨ destination + 96 ≤ offset)
    (atPoint : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 offset) point) :
    ProjectiveAt u (stackPtr s - BitVec.ofNat 64 offset) point :=
  atPoint.of_bytes_eq (fun _ hi => copy_byte pre agrees destBound destSaved ho hl apart hi)

theorem call_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {destination offset : Nat} {point resultPoint : Projective}
    (result : PointCallResult s t u boundary ret destination resultPoint)
    (ho : offset ≤ 2056) (hl : 96 ≤ offset + 8)
    (apart : offset + 96 ≤ destination ∨ destination + 96 ≤ offset)
    (atPoint : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 offset) point) :
    ProjectiveAt u (stackPtr s - BitVec.ofNat 64 offset) point :=
  atPoint.of_bytes_eq (fun _ hi => result.bytes offset 96 ho hl apart _ hi)

theorem add_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective} {outputOffset sourceOffset : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (outputBound : outputOffset ≤ 2056) (outputSaved : 144 ≤ outputOffset)
    (sourceBound : sourceOffset ≤ 2056) (sourceLength : 96 ≤ sourceOffset + 8)
    (apart : outputOffset + 96 ≤ sourceOffset ∨ sourceOffset + 96 ≤ outputOffset)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (src : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 sourceOffset)
    (leftAt : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 outputOffset) left)
    (rightAt : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 sourceOffset) right) :
    ∃ u, PointCallResult s t u boundary site.returnRip outputOffset (left.add right) := by
  have targetProg := inProgram_of_textOffset 0x51f0 (by decide)
  have step := scalar_call pre (by decide) (by decide) state site.offset site.disp
    (Nat.le_of_lt site.bounded) site.bytes
    (by rw [site.target_eq]; exact Program.inProgram_low targetProg)
    (by rw [site.target_eq]; exact targetProg) rip
  rw [site.target_eq] at step
  obtain ⟨v, run, ready, effect⟩ := step
  have stateV := state.after_call pre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = stackPtr s - BitVec.ofNat 64 sourceOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  let layout : StackCallLayout 3464 96 96 920 :=
    ⟨2064, sourceOffset, outputOffset, by decide, by decide,
      by omega, by omega, sourceLength, by omega, apart⟩
  have cp := CalleePre.of_stack pre layout stateV.bindingsSupported stateV.machine
    stateV.directionFlag stateV.loaded stateV.allocated effect.rip stateV.rsp srcV dstV
    (call_return_program site effect)
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    exact leftAt.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect
      outputBound (by omega) hi)
  have rightV : ProjectiveAt v (v.regValue .rsi) right := by
    rw [srcV]
    exact rightAt.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect
      sourceBound sourceLength hi)
  obtain ⟨u, result, value⟩ := Projective.projective_add_correct cp leftV rightV
  exact ⟨u, Projective.Multiply.Machine.Basepoint.TableSteps.finish_call
    pre state run ready effect dstV outputBound outputSaved (by decide) result value⟩

end P256.Proofs.Ecdh.Table
