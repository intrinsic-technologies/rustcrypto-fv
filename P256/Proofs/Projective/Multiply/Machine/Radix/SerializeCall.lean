import P256.Proofs.Projective.Multiply.Machine.Radix.Prepare
import P256.Proofs.Projective.Multiply.Machine.Radix.Scalar
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Correct
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

def serializeComponents (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.flags,.rip,
    .mem (stackPtr s-128) 8,.mem (stackPtr s-40) 32]

theorem serialize_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t)
    (scalar : Nat256At s (s.regValue .rsi) d)
    (rip : t.RIP = 0x10b77a) (source : t.regValue .rsi = s.regValue .rsi)
    (destination : t.regValue .rdi = stackPtr s-40) :
    ∃ u fuel, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x10b77f ∧
      Bytes u.external (stackPtr s-40) 32 (fun i => UInt8.ofNat (d/256^(31-i)%256)) ∧
      AgreesExcept (serializeComponents s) t u := by
  obtain ⟨entry,call,ready,loaded,effect,mem⟩ := call_rel32_exists pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary state.ready (state.loaded pre)
    state.agrees.grow 120 0xb77a 0x7721 state.rsp rip (by decide) (by decide)
    (by decide) (by decide +kernel) (inProgram_of_textOffset 0x12ea0 (by decide))
  have push : pushAddr t = stackPtr s-128 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have ripE : entry.RIP = 0x112ea0 := effect.rip
  have rspE : stackPtr entry = stackPtr s-128 := effect.writes.1.trans push
  have frameE : State s entry 128 := by
    apply state.after_stack pre ready effect.agrees
    · intro c hc hm
      simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl <;> simp_all [Component.isMem,registers]
    · intro p n hc
      simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false,
        reduceCtorEq,false_or,or_false,Component.mem.injEq] at hc
      obtain ⟨rfl,rfl⟩ := hc
      exact ⟨128,by decide,by decide,push⟩
    · exact rspE
  have sourceE : entry.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationE : entry.regValue .rdi = stackPtr s-40 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  change entry.external = memStore t.external (stackPtr s-128) (0x10b77f : BitVec 64) at mem
  have ret : (returnBoundary entry).rip = 0x10b77f := by
    change memLoad entry.external (stackPtr entry) 64 = _
    rw [rspE,mem,memLoad_memStore_same _ _ _ (by decide) (by decide)]
  have callee : CalleePre entry boundary 0x112ea0 32 32 8 :=
    CalleePre.of_input_and_stack pre
      (⟨128,40,by decide,by decide,by decide,by decide⟩ : StackBufferLayout 136 32 8)
      (bindingsSupported_of_ready_agrees pre.bindingsSupported ready frameE.agrees)
      (supportedMachine_of_ready_agrees pre.machine ready frameE.agrees)
      (frameE.agrees.directionFlagClear (by simp [components,registers]) pre.directionFlag)
      loaded frameE.agrees.grow ripE rspE sourceE destinationE
      (ret ▸ inProgram_of_textOffset 0xb77f (by decide))
  have scalarE : Nat256At entry (entry.regValue .rsi) d := by
    rw [sourceE]
    exact frameE.scalar pre scalar
  obtain ⟨u,result,bytes,_,ag⟩ := Serialize.scalar_encode_correct callee scalarE
  have rspU : stackPtr u = stackPtr s-120 := by
    have h : stackPtr u = stackPtr entry+8 := result.rsp
    rw [h,rspE]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have narrow : AgreesExcept (serializeComponents s) t u := by
    apply (effect.agrees.trans ag).mono
    simp only [pushEffect_components,leafComponents,destinationE,push,serializeComponents,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro c hc
    rcases hc with (rfl|rfl|rfl)|(((rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl))|(rfl|rfl))
    all_goals simp
  have stateU : State s u := by
    apply state.after_stack pre (readyToStep result.machine result.bindingsSupported) narrow
    · intro c hc hm
      simp only [serializeComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp_all [Component.isMem,registers]
    · intro p n hc
      simp only [serializeComponents,List.mem_cons,List.not_mem_nil,or_false,
        reduceCtorEq,false_or,Component.mem.injEq] at hc
      rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨128,by decide,by decide,rfl⟩
      · exact ⟨40,by decide,by decide,rfl⟩
    · exact rspU
  obtain ⟨fuel,run⟩ := result.execution
  exact ⟨u,1+fuel,call.trans run,stateU,result.rip.trans ret,destinationE ▸ bytes,narrow⟩

end P256.Proofs.Projective.Multiply.Machine.Radix
