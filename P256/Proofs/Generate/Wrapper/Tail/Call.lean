import P256.Proofs.Generate.Wrapper.Tail.State
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Correct
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem push_bytes {initial s t : RamState}
    (stack : Stack.Valid initial 4024)
    (agrees : AgreesExcept [.reg 4, .mem (stackPtr initial - 272) 8, .rip] s t)
    {offset len : Nat} (above : offset ≤ 264) (below : len ≤ offset+8)
    (i : Nat) (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c member covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · obtain ⟨j, hj, eq⟩ := covered
    exact stack_sub_apart stack (a := 272) (b := offset) (na := 8) (nb := len)
      (by decide) (by omega) (by decide) below (.inl (by omega)) j hj i hi eq.symm
  · exact covered.elim


def encodeLayout : StackCallLayout 4024 32 32 8 :=
  ⟨272,184,256,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem encode_call [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat} {point : Standards.SECG.ECC.Curve.Point}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : State initial s 264) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106db5) (src : s.regValue .rsi = stackPtr initial-184)
    (dst : s.regValue .rdi = stackPtr initial-256)
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (stackPtr initial-184) d)
    (affine : Sec1.AffineAt s (stackPtr initial-152) point) :
    ∃ t, State initial t 264 ∧ t.RIP = 0x106dba ∧
      Bytes t.external (stackPtr initial-256) 32
        (fun i => UInt8.ofNat (d / 256^(31-i) % 256)) ∧
      Sec1.AffineAt t (stackPtr initial-152) point := by
  obtain ⟨v,sv,effect,_⟩ := state.call_rel32 call outside 0x6db5 0xc0e6 rip
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x12ea0 (by decide))
  have push : pushAddr s = stackPtr initial-272 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have ag : AgreesExcept [.reg 4,.mem (stackPtr initial-272) 8,.rip] s v := by
    simpa only [pushEffect_components,push] using effect.agrees
  have srcV : v.regValue .rsi = stackPtr initial-184 :=
    (ag.read (n := 64) (r := 6) (by simp)).trans src
  have dstV : v.regValue .rdi = stackPtr initial-256 :=
    (ag.read (n := 64) (r := 7) (by simp)).trans dst
  have ret : (returnBoundary v).rip = 0x106dba := (callEffect_stack effect).1
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside encodeLayout sv.bindingsSupported sv.machine sv.directionFlag sv.loaded
    sv.allocated effect.rip sv.rsp srcV dstV
    (ret ▸ inProgram_of_textOffset 0x6dba (by decide))
  have scalarV : SecretKeyFromBytes.Scalar.Nat256At v (v.regValue .rsi) d := by
    rw [srcV]
    exact ⟨scalar.1,fun i hi => (push_bytes call.stackAvailable.1 ag
      (by decide) (by decide) i hi).trans (scalar.2 i hi)⟩
  obtain ⟨t,result,encoded,_,frame⟩ :=
    Projective.Multiply.Machine.Radix.Serialize.scalar_encode_correct pre scalarV
  refine ⟨t,sv.after_callee call result dstV (by decide) (by decide) (by decide)
    (by decide),result.rip.trans ret,dstV ▸ encoded,?_⟩
  apply affine.of_bytes_eq
  intro i hi
  refine (frame.byte ?_).trans (push_bytes call.stackAvailable.1 ag
    (by decide) (by decide) i hi)
  intro c hc covered
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨j,hj,eq⟩ := leaf_covers hc covered
    rw [dstV] at eq
    exact stack_sub_apart call.stackAvailable.1 (a := 256) (b := 152)
      (na := 32) (nb := 65) (by decide) (by decide) (by decide) (by decide)
      (.inl (by decide)) j hj i hi eq.symm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl <;> exact covered.elim

end P256.Proofs.Generate.Wrapper
