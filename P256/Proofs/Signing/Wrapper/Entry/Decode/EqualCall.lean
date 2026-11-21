import P256.Proofs.Signing.Wrapper.Entry.Decode.EqualEntry
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Correct
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

structure EqualState [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520, Saved initial s where
  rip : s.RIP = 0x1025d9
  status : (s.regValue .rax).setWidth 8 = 0
  value : Nat256At s (stackPtr initial-240) (Arith.uint secret)

theorem nat256_preserved {s t : RamState} {address : BitVec 64} {d : Nat} {cs : List Component}
    (scalar : Nat256At s address d) (agrees : AgreesExcept cs s t)
    (apart : ∀ p n, Component.mem p n ∈ cs → RangeApart p n address 32) :
    Nat256At t address d := by
  refine ⟨scalar.1,fun i hi => ?_⟩
  rw [agrees.byte]
  · exact scalar.2 i hi
  · intro c hc covered
    cases c <;> try exact covered.elim
    rename_i p n
    obtain ⟨j,hj,eq⟩ := covered
    exact apart p n hc j hj i hi eq.symm

theorem equal_call [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : EqualEntry initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ EqualState initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have avoids : (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    by simpa only [signingKeyTrySign] using call_stack_avoids call
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨a,ha,ra,la,ea,_⟩ := call_rel32_exists hs avoids outside
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    520 0x25d4 0x16c97 state.rsp state.rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x19270 (by decide))
  have push : pushAddr s = stackPtr initial-528 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have fa : AgreesExcept [.reg 4,.mem (stackPtr initial-528) 8,.rip] s a := by
    simpa only [pushEffect_components,push] using ea.agrees
  have rsp : stackPtr a = stackPtr initial-528 := ea.writes.1.trans push
  have left : a.regValue .rdi = stackPtr initial-240 :=
    (fa.read (n:=64) (r:=7) (by simp)).trans state.left
  have right : a.regValue .rdx = stackPtr initial-344 :=
    (fa.read (n:=64) (r:=2) (by simp)).trans state.right
  have ret : (returnBoundary a).rip = 0x1025d9 := (callEffect_stack ea).1
  have grown := fun p hp => fa.grow p (state.allocated p hp)
  have pre : Equal.Pre a (returnBoundary initial) := by
    refine ⟨ra,la,ea.rip,?_,?_,?_,?_,?_,outside,?_⟩
    · exact (fa.read (n:=64) (r:=6) (by simp)).trans state.leftLength
    · exact (fa.read (n:=64) (r:=1) (by simp)).trans state.rightLength
    · rw [left]
      exact readable_of_grow (stack_sub_readable hs (offset:=240) (len:=32)
        (by decide) (by decide)) grown
    · rw [right]
      exact readable_of_grow (stack_sub_readable hs (offset:=344) (len:=32)
        (by decide) (by decide)) grown
    · rw [rsp]
      exact readable_of_grow (stack_sub_readable hs (offset:=528) (len:=8)
        (by decide) (by decide)) grown
    · rw [ret]
      exact inProgram_of_textOffset 0x25d9 (by decide)
  have apart (off len : Nat) (bound : off ≤ 520) (extent : len ≤ off+8) :
      ∀ p n, Component.mem p n ∈ [.reg 4,.mem (stackPtr initial-528) 8,.rip] →
        RangeApart p n (stackPtr initial-BitVec.ofNat 64 off) len := by
    intro p n member
    have h : p=stackPtr initial-528 ∧ n=8 := by simpa using member
    obtain ⟨rfl,rfl⟩ := h
    exact stack_sub_apart hs (a:=528) (b:=off) (by decide) (by omega)
      (by decide) extent (.inl (by omega))
  have valueA := nat256_preserved state.value fa (apart 240 32 (by decide) (by decide))
  have zeroA := nat256_preserved state.zero fa (apart 344 32 (by decide) (by decide))
  have eqValue := Equal.prefixEqual_nat256 (left ▸ valueA) (right ▸ zeroA)
  obtain ⟨t,result,status⟩ := Equal.equal_correct pre
  obtain ⟨n,ht⟩ := result.execution
  have ag := fa.trans result.agrees
  have sp : stackPtr t = stackPtr s := result.rsp.trans (callEffect_stack ea).2
  have st := state.toState.after_effect call (ha.trans ht) result.ready ag
    (by
      intro c hc p hp
      cases c <;> try exact hp.elim
      rename_i addr len
      have h : addr=stackPtr initial-528 ∧ len=8 := by
        simpa [Equal.clobbers] using hc
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨workRegion initial,by simp,work_contains hs (offset:=528) (by decide) (by decide) hp⟩)
    (sp.trans state.rsp) (by simp [Equal.clobbers])
  have mem := result.memory
  have read (off : Nat) (bound : off ≤ 520) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    rw [mem]
    exact memLoad_agrees_apart fa (apart off 8 bound (by omega))
  refine ⟨1+n,t,ha.trans ht,⟨st,?_,result.rip.trans ret,?_,?_⟩⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (ag.read (n:=64) (r:=12) (by simp [Equal.clobbers])).trans state.pointers
    · exact (ag.read (n:=64) (r:=13) (by simp [Equal.clobbers])).trans state.count
    · exact (read 192 (by decide)).trans state.lengths
    · exact (read 208 (by decide)).trans state.output
    · exact (read 200 (by decide)).trans state.capacity
  · have positive := ((arguments_iff secret message).mp call.argumentsValid).2.1
    rw [eqValue,decide_eq_false (by omega : Arith.uint secret ≠ 0)] at status
    exact status
  · simpa only [Nat256At,mem] using valueA

end P256.Proofs.Signing.Wrapper.Entry.Decode
