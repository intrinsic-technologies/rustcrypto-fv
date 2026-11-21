import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YCorrect
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XCorrect
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Decoded
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open Standards.SECG.ECC.Encoding

theorem canonical_value [Bindings] {s t u : RamState} {y : Bool} {x : Nat}
    (state : Frame s t) (agrees : AgreesExcept (Canonical.components y t) t u)
    (raw : Nat256At t (stackPtr s - 592) x) : Nat256At u (stackPtr s - 592) x := by
  refine ⟨raw.1, fun i hi => ?_⟩
  have preserved := effect_byte agrees (off := 168) (len := 32) (by decide) (by
    intro c hc hm
    cases y <;> simp only [Canonical.components, Bool.false_eq_true, ↓reduceIte,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with ((rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    all_goals first | (solve | simp [Component.isMem] at hm) | exact ⟨16,8,rfl,by decide,.inl (by decide)⟩) hi
  have addr : stackPtr t + 168 = stackPtr s - 592 := stack_address state (by decide)
  change u.external[stackPtr t + 168 + BitVec.ofNat 64 i]? =
    t.external[stackPtr t + 168 + BitVec.ofNat 64 i]? at preserved
  rw [addr] at preserved
  exact preserved.trans (raw.2 i hi)

def coordinateComponents (y : Bool) (t : RamState) : List Component :=
  decodeComponents y t ++ Canonical.components y t

theorem canonical_correct [Bindings] (y : Bool) {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (size : bytes.size = 65) (rip : t.RIP = if y then 0x110635 else 0x110820)
    (source : (if y then t.regValue .rsi else t.regValue .rbp) = s.regValue .rsi)
    (constants : y = false → t.regValue .r15 = 0xffffffff00000001 ∧
      t.regValue .r12 = 0xffffffff ∧ t.regValue .r13 = 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = (if y then 0x110704 else 0x1108d8) ∧
      Nat256At u (stackPtr s - 592)
        (octetsToNat (bytes.extract (if y then 33 else 1) (if y then 65 else 33))) ∧
      (if y then u.regValue .r14 else u.regValue .rbp) =
        (if octetsToNat (bytes.extract (if y then 33 else 1) (if y then 65 else 33)) < Operations.domain.p then 1 else 0) ∧
      (y = true → u.regValue .r15 = 0xffffffff00000001 ∧
        u.regValue .r12 = 0xffffffff ∧ u.regValue .r13 = 0) ∧
      AgreesExcept (coordinateComponents y t) t u := by
  obtain ⟨n,a,ra,fa,ia,raw,limbs,ga⟩ := decode_correct y pre state size rip source
  have rsp : stackPtr a = stackPtr t := fa.rsp.trans state.rsp.symm
  have compose {u : RamState} (h : AgreesExcept (Canonical.components y a) a u) :
      AgreesExcept (coordinateComponents y t) t u := by
    have eq : Canonical.components y a = Canonical.components y t := by
      simp only [Canonical.components, rsp]
    rw [eq] at h
    exact ga.trans h
  cases y with
  | false =>
    have keep (r : BitVec 5) (hr : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 6 ∧ r ≠ 2) :
        (Operand.reg r : Operand 64).read a = (Operand.reg r : Operand 64).read t :=
      ga.read (by simpa [decodeComponents, storeComponents, BitVec.ofNat_eq_ofNat] using hr)
    obtain ⟨m,u,ru,fu,iu,valid,gu⟩ := Canonical.x_correct pre fa ia
      ((keep 15 (by decide)).trans (constants rfl).1)
      ((keep 12 (by decide)).trans (constants rfl).2.1)
      ((keep 13 (by decide)).trans (constants rfl).2.2)
    have val : (Canonical.xInput a).toNat = octetsToNat (bytes.extract 1 33) := limbs
    rw [val] at valid
    exact ⟨n+m,u,ra.trans ru,fu,iu,canonical_value fa gu raw,valid,
      (by intro h; cases h),compose gu⟩
  | true =>
    obtain ⟨m,u,ru,fu,iu,valid,r15,r12,r13,gu⟩ := Canonical.y_correct pre fa ia
    have val : (Canonical.yInput a).toNat = octetsToNat (bytes.extract 33 65) := limbs
    rw [val] at valid
    exact ⟨n+m,u,ra.trans ru,fu,iu,canonical_value fa gu raw,valid,
      fun _ => ⟨r15,r12,r13⟩,compose gu⟩

theorem coordinate_byte [Bindings] {s t u : RamState} {y : Bool}
    (state : Frame s t) (agrees : AgreesExcept (coordinateComponents y t) t u)
    {off len : Nat} (pair : (off,len) ∈ [(312,32),(748,1)]) {i : Nat} (hi : i < len) :
    u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  have cases : (off=312 ∧ len=32) ∨ (off=748 ∧ len=1) := by simpa using pair
  rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have h := effect_byte agrees (off := 448) (len := 32) (by decide) (by
      intro c hc hm
      simp only [coordinateComponents, List.mem_append] at hc
      rcases hc with hc | hc
      · simp only [decodeComponents,storeComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
        all_goals try { simp only [Component.isMem,Bool.false_eq_true] at hm }
        · exact ⟨168,8,rfl,by decide,by decide⟩
        · exact ⟨176,8,rfl,by decide,by decide⟩
        · exact ⟨184,8,rfl,by decide,by decide⟩
        · exact ⟨192,8,rfl,by decide,by decide⟩
      · cases y <;> simp only [Canonical.components,Bool.false_eq_true,↓reduceIte,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
        all_goals rcases hc with ((rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
        all_goals first | (solve | simp only [Component.isMem,Bool.false_eq_true] at hm) | exact ⟨16,8,rfl,by decide,by decide⟩) hi
    first
    | have addr : stackPtr t+448#64=stackPtr s-312#64 := stack_address state (by decide)
      rw [addr] at h
      exact h
    | have addr : stackPtr t+12#64=stackPtr s-748#64 := stack_address state (by decide)
      rw [addr] at h
      exact h

  · have h := effect_byte agrees (off := 12) (len := 1) (by decide) (by
      intro c hc hm
      simp only [coordinateComponents, List.mem_append] at hc
      rcases hc with hc | hc
      · simp only [decodeComponents,storeComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
        all_goals try { simp only [Component.isMem,Bool.false_eq_true] at hm }
        · exact ⟨168,8,rfl,by decide,by decide⟩
        · exact ⟨176,8,rfl,by decide,by decide⟩
        · exact ⟨184,8,rfl,by decide,by decide⟩
        · exact ⟨192,8,rfl,by decide,by decide⟩
      · cases y <;> simp only [Canonical.components,Bool.false_eq_true,↓reduceIte,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
        all_goals rcases hc with ((rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
        all_goals first | (solve | simp only [Component.isMem,Bool.false_eq_true] at hm) | exact ⟨16,8,rfl,by decide,by decide⟩) hi
    first
    | have addr : stackPtr t+448#64=stackPtr s-312#64 := stack_address state (by decide)
      rw [addr] at h
      exact h
    | have addr : stackPtr t+12#64=stackPtr s-748#64 := stack_address state (by decide)
      rw [addr] at h
      exact h

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
