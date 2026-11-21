import P256.Proofs.Ecdh.Initial.State
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall Field
open P256.Proofs.Common.Field (AdvanceTriple)

theorem frame_address (s : RamState) (offset : Nat) (bound : offset ≤ 2056) :
    frameBase s + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (2056-offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 2056 offset (by omega) bound]
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {bytes : List UInt8} {effect : RamState → Effect}
    (state : Ecdh.Frame s t)
    (block : AdvanceTriple boundary (fun t => t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post effect))
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (noMem : ∀ c ∈ (effect t).components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ (effect t).components)
    (hdf : Component.df ∉ (effect t).components)
    (hmxcsr : Component.mxcsr ∉ (effect t).components)
    (hfcw : Component.fcw ∉ (effect t).components) :
    ∃ fuel u, Advances boundary fuel t u ∧ Ecdh.Frame s u ∧
      (effect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel,u,run,ready,_,result⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code) rip
  exact ⟨fuel,u,run,state.after_registers ready result.agrees noMem sp hdf hmxcsr hfcw,
    result,result.agrees.external noMem⟩

structure SelectResult [Bindings] (s t u : RamState) (boundary : ReturnBoundary)
    (ret : BitVec 64) (destination value : Nat) : Prop extends Ecdh.Frame s u where
  execution : ∃ fuel, Advances boundary fuel t u
  rip : u.RIP = ret
  value : MontgomeryAt u (stackPtr s - BitVec.ofNat 64 destination) value
  registers : ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r
  bytes : ∀ offset len, offset ≤ 2056 → len ≤ offset+8 →
    (offset+32 ≤ destination ∨ destination+len ≤ offset) →
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?

theorem SelectResult.memory [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {destination value offset x : Nat}
    (result : SelectResult s t u boundary ret destination value)
    (bound : offset ≤ 2056) (length : 24 ≤ offset)
    (apart : offset+32 ≤ destination ∨ destination+32 ≤ offset)
    (input : MontgomeryAt t (stackPtr s-BitVec.ofNat 64 offset) x) :
    MontgomeryAt u (stackPtr s-BitVec.ofNat 64 offset) x :=
  input.of_bytes_eq (result.bytes offset 32 bound (by omega) apart)

theorem SelectResult.scalar [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {destination value : Nat}
    (result : SelectResult s t u boundary ret destination value) (bound : destination+8 ≤ 2048) :
    memLoad u.external (frameBase s+8) 64 = memLoad t.external (frameBase s+8) 64 := by
  rw [show frameBase s+8 = stackPtr s-BitVec.ofNat 64 2048 from frame_address s 8 (by decide)]
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s-2048#64+BitVec.ofNat 64 i]?).getD 0 = _
  rw [result.bytes 2048 8 (by decide) (by decide) (.inr bound) i hi]
  rfl

theorem select_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {select : Bool} (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t)
    (site : BinaryCallSite 3464 2056 0x114380 128)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) x)
    (hy : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.rightOffset) y)
    (choice : (t.regValue .rcx).setWidth 8 = if select then 1 else 0) :
    ∃ u, SelectResult s t u boundary
      (Extracted.textAddress+BitVec.ofNat 64 site.codeOffset+5)
      site.layout.outputOffset (if select then y else x) := by
  obtain ⟨fuel,u,run,frame,rip,value,saved,bytes,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if select then y else x) pre.toCalleePre state site
    (fun v hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (fun w : BitVec 64 => w.setWidth 8) hc).trans choice))
    rip input right output hx hy
  exact ⟨u,frame,⟨fuel,run⟩,rip,value,saved,bytes⟩

def firstSite : BinaryCallSite 3464 2056 0x114380 128 :=
  ⟨0x101,0x1427a,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨2064,1808,272,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,1040,by decide,by decide,by decide⟩

def secondSite : BinaryCallSite 3464 2056 0x114380 128 :=
  ⟨0x11b,0x14260,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨2064,1776,240,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,1008,by decide,by decide,by decide⟩

def thirdSite : BinaryCallSite 3464 2056 0x114380 128 :=
  ⟨0x135,0x14246,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨2064,1744,208,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,976,by decide,by decide,by decide⟩

end P256.Proofs.Ecdh.Initial
