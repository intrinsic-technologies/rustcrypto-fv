import P256.Proofs.Verifying.Core.Normalize.CoordinateSetup
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Field.Montgomery
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize.Coordinates

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program FieldCall

def xSite : BinaryCallSite 9992 1176 0x113890 280 :=
  ⟨0xdef3,0x5998,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x13890 (by decide),
    ⟨1184,1048,600,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩,
    rfl,by decide,80,by decide,by decide,Or.inr (by decide)⟩

def ySite : BinaryCallSite 9992 1176 0x113890 280 :=
  ⟨0xdf3f,0x594c,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x13890 (by decide),
    ⟨1184,1048,784,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩,
    rfl,by decide,80,by decide,by decide,Or.inr (by decide)⟩

theorem x_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x reciprocal : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dedd)
    (left : Field.MontgomeryAt t (stackPtr s-1048) x)
    (right : Field.MontgomeryAt t (stackPtr s-80) reciprocal)
    (r14 : t.regValue .r14 = stackPtr s-80) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10def8 ∧
      Field.MontgomeryAt u (stackPtr s-600) (x*reciprocal % Operations.domain.p) ∧
      u.regValue .r15 = stackPtr s-600 ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r14],u.regValue r = t.regValue r) ∧
      (∀ offset len, offset ≤ 1176 → len ≤ offset+8 →
        (offset+32 ≤ 600 ∨ 600+len ≤ offset) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) := by
  obtain ⟨n,a,runA,stateA,effect,memory⟩ := x_setup pre state rip
  have values := effect.writes
  simp only [xSetupEffect,Write.AllHold] at values
  have dst : stackPtr t+576 = stackPtr s-600 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have src : stackPtr t+128 = stackPtr s-1048 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have leftA := left.of_bytes_eq (fun i hi => by rw [memory])
  have rightA := right.of_bytes_eq (fun i hi => by rw [memory])
  obtain ⟨m,u,runU,stateU,ripU,value,regs,bytes,_⟩ := binary_call (x := x) (y := reciprocal) (op := fun a b => a*b % Operations.domain.p) pre.toCalleePre stateA xSite
    (fun v cp hx hy => Field.field_mul_correct cp hx hy) effect.rip
    (values.2.2.1.trans src) (values.2.2.2.trans r14) (values.2.1.trans dst) leftA rightA
  refine ⟨n+m,u,runA.trans runU,stateU,ripU,value,(regs .r15 (by simp)).trans (values.1.trans dst),?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact (regs .rbx (by simp)).trans
        (effect.agrees.read (n := 64) (r := 3) (by simp [xSetupEffect,Effect.components]))
    · exact (regs .rbp (by simp)).trans
        (effect.agrees.read (n := 64) (r := 5) (by simp [xSetupEffect,Effect.components]))
    · exact (regs .r14 (by simp)).trans
        (effect.agrees.read (n := 64) (r := 14) (by simp [xSetupEffect,Effect.components]))
  · intro offset len bound length apart i hi
    exact (bytes offset len bound length apart i hi).trans (by rw [memory])

theorem y_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {y reciprocal : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10df2c)
    (left : Field.MontgomeryAt t (stackPtr s-1048) y)
    (right : Field.MontgomeryAt t (stackPtr s-80) reciprocal)
    (r14 : t.regValue .r14 = stackPtr s-80) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10df44 ∧
      Field.MontgomeryAt u (stackPtr s-784) (y*reciprocal % Operations.domain.p) ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r14,.r15],u.regValue r = t.regValue r) ∧
      (∀ offset len, offset ≤ 1176 → len ≤ offset+8 →
        (offset+32 ≤ 784 ∨ 784+len ≤ offset) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) := by
  obtain ⟨n,a,runA,stateA,effect,memory⟩ := y_setup pre state rip
  have values := effect.writes
  simp only [ySetupEffect,Write.AllHold] at values
  have dst : stackPtr t+392 = stackPtr s-784 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have src : stackPtr t+128 = stackPtr s-1048 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have leftA := left.of_bytes_eq (fun i hi => by rw [memory])
  have rightA := right.of_bytes_eq (fun i hi => by rw [memory])
  obtain ⟨m,u,runU,stateU,ripU,value,regs,bytes,_⟩ := binary_call (x := y) (y := reciprocal) (op := fun a b => a*b % Operations.domain.p) pre.toCalleePre stateA ySite
    (fun v cp hx hy => Field.field_mul_correct cp hx hy) effect.rip
    (values.2.1.trans src) (values.2.2.trans r14) (values.1.trans dst) leftA rightA
  refine ⟨n+m,u,runA.trans runU,stateU,ripU,value,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact (regs .rbx (by simp)).trans
        (effect.agrees.read (n := 64) (r := 3) (by simp [ySetupEffect,Effect.components]))
    · exact (regs .rbp (by simp)).trans
        (effect.agrees.read (n := 64) (r := 5) (by simp [ySetupEffect,Effect.components]))
    · exact (regs .r14 (by simp)).trans
        (effect.agrees.read (n := 64) (r := 14) (by simp [ySetupEffect,Effect.components]))
    · exact (regs .r15 (by simp)).trans
        (effect.agrees.read (n := 64) (r := 15) (by simp [ySetupEffect,Effect.components]))
  · intro offset len bound length apart i hi
    exact (bytes offset len bound length apart i hi).trans (by rw [memory])

end P256.Proofs.Verifying.Core.Normalize.Coordinates
