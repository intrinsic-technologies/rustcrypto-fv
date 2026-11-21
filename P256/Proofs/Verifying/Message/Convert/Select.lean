import P256.Proofs.Verifying.Message.Interface
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall Field

structure SelectResult [Bindings] (s t u : RamState) (boundary : ReturnBoundary)
    (ret : BitVec 64) (destination value : Nat) : Prop extends Message.Frame s u where
  execution : ∃ fuel, Advances boundary fuel t u
  rip : u.RIP = ret
  value : MontgomeryAt u (stackPtr s - BitVec.ofNat 64 destination) value
  writes : MemoryWriteFrame t u #v[ScalarFrame.workRegion s 9992]
  registers : ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r
  bytes : ∀ offset len, offset ≤ 1176 → len ≤ offset+8 →
    (offset+32 ≤ destination ∨ destination+len ≤ offset) →
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?

theorem SelectResult.memory [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {destination value offset x : Nat}
    (result : SelectResult s t u boundary ret destination value)
    (bound : offset ≤ 1176) (length : 24 ≤ offset)
    (apart : offset+32 ≤ destination ∨ destination+32 ≤ offset)
    (input : MontgomeryAt t (stackPtr s-BitVec.ofNat 64 offset) x) :
    MontgomeryAt u (stackPtr s-BitVec.ofNat 64 offset) x :=
  input.of_bytes_eq (result.bytes offset 32 bound (by omega) apart)

theorem select_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {select : Bool} (pre : CalleePre s boundary 0x10d570 72 24 9992) (state : Message.Frame s t)
    (site : BinaryCallSite 9992 1176 0x114380 128)
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
  obtain ⟨fuel,u,run,frame,rip,value,saved,bytes,writes⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if select then y else x) pre state site
    (fun v hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (fun w : BitVec 64 => w.setWidth 8) hc).trans choice))
    rip input right output hx hy
  exact ⟨u,frame,⟨fuel,run⟩,rip,value,writes,saved,bytes⟩

def firstSite : BinaryCallSite 9992 1176 0x114380 128 :=
  ⟨0xda14,0x6967,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨1184,1176,176,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,1048,by decide,by decide,by decide⟩

def secondSite : BinaryCallSite 9992 1176 0x114380 128 :=
  ⟨0xda2e,0x694d,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨1184,1144,144,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,1016,by decide,by decide,by decide⟩

def thirdSite : BinaryCallSite 9992 1176 0x114380 128 :=
  ⟨0xda48,0x6933,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨1184,1112,112,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,984,by decide,by decide,by decide⟩

end P256.Proofs.Verifying.Message.Convert
