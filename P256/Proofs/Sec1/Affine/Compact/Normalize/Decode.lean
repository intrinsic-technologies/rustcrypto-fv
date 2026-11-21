import P256.Proofs.Sec1.Affine.Compact.Normalize.State
import P256.Proofs.Sec1.Affine.Compact.Normalize.Arguments
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Field.Decode

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame FieldCall SecretKeyFromBytes.Scalar

inductive DecodeSite | original | negative

def DecodeSite.pc : DecodeSite → BitVec 64
  | .original => 0x1103b8
  | .negative => 0x1103c8

def DecodeSite.callOffset : DecodeSite → Nat
  | .original => 0x103c3
  | .negative => 0x103d3

def DecodeSite.disp : DecodeSite → BitVec 32
  | .original => 0x3e78
  | .negative => 0x3e68

def DecodeSite.inputOffset : DecodeSite → Nat
  | .original => 632
  | .negative => 560

def DecodeSite.outputOffset : DecodeSite → Nat
  | .original => 184
  | .negative => 416

def DecodeSite.value (site : DecodeSite) (point : Option Curve.Point) : Nat :=
  match site with
  | .original => Select.yCoordinate point
  | .negative => Spec.Points.negElement (Select.yCoordinate point)

def DecodeSite.layout (site : DecodeSite) : StackCallLayout 3360 32 32 40 :=
  ⟨768,site.inputOffset,site.outputOffset,by decide,by decide,
    by cases site <;> decide,by cases site <;> decide,by cases site <;> decide,
    by cases site <;> decide,by cases site <;> decide⟩

def DecodeSite.bytes : DecodeSite → List UInt8
  | .original => firstDecodeBytes
  | .negative => secondDecodeBytes

def DecodeSite.effect : DecodeSite → RamState → Effect
  | .original => firstDecodeEffect
  | .negative => secondDecodeEffect

theorem decode_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (site : DecodeSite) :
    SignatureFromDer.Parser.ReadSlice.AdvancesBlock boundary (fun s => s.RIP = site.pc)
      (codeRange site.pc site.bytes) site.effect := by
  cases site
  · exact firstDecode_setup boundary outside
  · exact secondDecode_setup boundary outside

theorem decode_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes) (site : DecodeSite)
    (state : Normalizing s t point site.pc) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Normalizing s u point (Extracted.textAddress + BitVec.ofNat 64 site.callOffset + 5) ∧
      Nat256At u (stackPtr s-BitVec.ofNat 64 site.outputOffset) (site.value point) ∧
      (∀ offset len : Nat, offset ≤ 760 → len ≤ offset+8 →
        (offset+32 ≤ site.outputOffset ∨ site.outputOffset+len ≤ offset) →
        ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) := by
  have code := programText_slice (programLoaded_codeIn state.loaded)
    (site.pc.toNat-0x100000) site.bytes (by cases site <;> decide) (by cases site <;> decide +kernel)
  have codeAddress : Extracted.textAddress + BitVec.ofNat 64 (site.pc.toNat-0x100000) = site.pc := by
    cases site <;> decide
  rw [codeAddress] at code
  obtain ⟨n,v,runV,readyV,_,effect⟩ := decode_setup boundary pre.outerBoundary site t
    (readyToStep state.machine state.bindingsSupported) code state.rip
  have agrees : AgreesExcept [.reg 7,.reg 6,.rip] t v := by
    cases site <;> exact effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := state.toFrameState.after_registers readyV agrees
    (by simp [Component.Covers]) (by simp)
  have vin : v.regValue .rsi = stackPtr s-BitVec.ofNat 64 site.inputOffset := by
    cases site
    · exact effect.writes.2.trans state.r12
    · exact effect.writes.2.trans state.r15
  have vout : v.regValue .rdi = stackPtr s-BitVec.ofNat 64 site.outputOffset := by
    cases site
    · exact effect.writes.1.trans (scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide))
    · exact effect.writes.1.trans (scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide))
  have value : Field.MontgomeryAt v (stackPtr s-BitVec.ofNat 64 site.inputOffset) (site.value point) := by
    cases site
    · exact state.y.of_bytes_eq (fun i hi => by rw [memory]; rfl)
    · exact state.negative.of_bytes_eq (fun i hi => by rw [memory]; rfl)
  obtain ⟨m,u,runU,frameU,ripU,canonical,saved,kept,_⟩ := unary_call
    (resultAt := fun u address => Nat256At u address (site.value point))
    pre.toCalleePre frame site.layout rfl (by cases site <;> decide)
    site.callOffset site.disp (by cases site <;> decide) (by cases site <;> decide +kernel)
    (by cases site <;> decide) (by decide) (inProgram_of_textOffset 0x14240 (by decide))
    (fun v hp hx => Field.field_decode_correct hp hx)
    (by cases site <;> exact effect.rip) vin vout value
  have keep {offset len : Nat} (ho : offset ≤ 760) (hl : len ≤ offset+8)
      (apart : offset+32 ≤ site.outputOffset ∨ site.outputOffset+len ≤ offset) :
      ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept offset len ho hl apart i hi).trans (by rw [memory])
  have regs (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      u.regValue r = t.regValue r := by
    apply (saved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact agrees.read (n := 64) (r := 3) (by simp)
    · exact agrees.read (n := 64) (r := 5) (by simp)
    · exact agrees.read (n := 64) (r := 12) (by simp)
    · exact agrees.read (n := 64) (r := 13) (by simp)
    · exact agrees.read (n := 64) (r := 14) (by simp)
    · exact agrees.read (n := 64) (r := 15) (by simp)
  refine ⟨n+m,u,runV.trans runU,?_,canonical,fun off len ho hl ha => keep ho hl ha⟩
  refine ⟨frameU,ripU,(regs .rbx (by simp)).trans state.output,?_,?_,?_,
    (regs .r12 (by simp)).trans state.r12,(regs .r15 (by simp)).trans state.r15,
    (regs .r13 (by simp)).trans state.zero,
    (congrArg (BitVec.setWidth 8) (regs .rbp (by simp))).trans state.choice,
    (congrArg (BitVec.setWidth 8) (regs .r14 (by simp))).trans state.infinity,?_⟩
  · exact state.x.of_bytes_eq (keep (by decide) (by decide) (by cases site <;> decide))
  · exact state.y.of_bytes_eq (keep (by decide) (by decide) (by cases site <;> decide))
  · exact state.negative.of_bytes_eq (keep (by decide) (by decide) (by cases site <;> decide))
  · apply Eq.trans _ state.mask
    apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0
    simpa only [BitVec.ofNat_eq_ofNat] using congrArg (fun v : Option UInt8 => v.getD 0)
      (keep (offset := 748) (len := 1) (by decide) (by decide) (by cases site <;> decide) i hi)


theorem decode_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : ReadyDecode s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Decoded s u point := by
  obtain ⟨n,a,runA,stateA,canonicalY,_⟩ := decode_stage pre .original state
  obtain ⟨m,u,runU,stateU,canonicalNegative,kept⟩ := decode_stage pre .negative stateA
  refine ⟨n+m,u,runA.trans runU,stateU,?_,canonicalNegative⟩
  refine ⟨canonicalY.1,fun i hi => ?_⟩
  exact (kept 184 32 (by decide) (by decide) (Or.inl (by decide)) i hi).trans (canonicalY.2 i hi)

end P256.Proofs.Sec1.Affine.Compact.Normalize
