import P256.Proofs.Program.Call
import P256.Proofs.Signing.Wrapper.Entry.Decode.State
import P256.Proofs.SecretKeyFromBytes.Choice

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def choiceClobbers (s : RamState) : List Component :=
  [.reg 0,.reg 4,.flags,.rip,.mem (stackPtr s-528) 8,.mem (stackPtr s-529) 1]

theorem choice_call [bindings : Bindings] {s t : RamState} {input message : ByteArray}
    (hc : ValidCall signingKeyTrySign s [input,message])
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s) (state : State s t 520)
    (offset : Nat) (disp : BitVec 32) (bound : offset+5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ u, Advances (returnBoundary s) 6 t u ∧ State s u 520 ∧ u.RIP = Extracted.textAddress+BitVec.ofNat 64 offset+5#64 ∧
      u.regValue .rax = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (choiceClobbers s) t u := by
  obtain ⟨slices,call⟩ := hc
  have hc : ValidCall signingKeyTrySign s [input,message] := ⟨slices,call⟩
  have hs : Stack.Valid s 5112 := call.stackAvailable.1
  have hout := outer_boundary call hm hb
  let p := Extracted.textAddress + BitVec.ofNat 64 offset
  have hp : pushAddr t = stackPtr s - BitVec.ofNat 64 (528) := by simp only [pushAddr, state.rsp, BitVec.sub_sub]; rfl
  obtain ⟨v,hv,rv,loadedv,ev,memv⟩ := call_rel32_exists hs (by simpa only [signingKeyTrySign] using call_stack_avoids call) hout
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    520 offset disp state.rsp rip (by decide) (by decide) (by omega) bytes
    (by rw [target]; exact inProgram_of_textOffset 0x19070 (by decide))
  have ev' : (callEffect (fun _ => 0x119070) (p + 5#64) t).Holds t v := by
    change (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64)) (p + 5#64) t).Holds t v at ev
    rw [target] at ev
    exact ev
  have spv : stackPtr v = stackPtr s - BitVec.ofNat 64 (528) := ev'.writes.1.trans hp
  have topv : stackTop v = p + 5#64 := (callEffect_stack ev').1
  have fv : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 (528)) 8, .rip] t v := by
    simpa only [pushEffect_components, hp] using ev'.agrees
  have allocatedv := fun a ha => ev'.agrees.grow a (state.allocated a ha)
  have subOne : BitVec.ofNat 64 (528) + 1 = BitVec.ofNat 64 (529) := rfl
  have chip : InProgram (p + 5#64) := by
    have h := inProgram_of_textOffset (offset + 5) bound
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, p] using h
  have cp : ChoicePre v := by
    refine ⟨ev'.rip, ?_, ?_, ?_, ?_⟩
    · rw [spv, BitVec.sub_sub, subOne]
      exact P256.Proofs.Program.writable_of_grow
        (P256.Proofs.Program.stack_sub_writable hs
          (fun a ha hpt => call_stack_avoids call a ha (.inr hpt)) (offset := 529) (len := 1) (by omega) (by omega)
          (by decide) (by have h := Nat.mod_lt (stackPtr s - BitVec.ofNat 64 (529)).toNat (by decide : 0 < 4096); omega)) allocatedv
    · rw [spv]
      exact P256.Proofs.Program.readable_of_grow
        (P256.Proofs.Program.stack_sub_readable hs (by omega) (by omega)) allocatedv
    · rw [topv]
      exact P256.Proofs.Program.inProgram_low chip
    · rw [spv, BitVec.sub_sub, subOne]
      intro i hi j hj he
      apply (call.separation.2 (callStack signingKeyTrySign s) (by simp)).2 _
        (stack_component_within call.stackAvailable.1 (offset := 529) (len := 1) (by decide) (by decide) ⟨i,hi,rfl⟩)
      left
      change stackPtr s - BitVec.ofNat 64 (529) + BitVec.ofNat 64 i = _ at he
      rw [he]
      have h := inProgram_of_textOffset (0x19070 + j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h

  obtain ⟨u, hu, ru, eu⟩ := choice_correct rv (choice_code_loaded loadedv) cp (by
    intro q hq
    apply boundary_ne_program hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact inProgram_of_textOffset 0x19074 (by decide)
    · exact inProgram_of_textOffset 0x19078 (by decide)
    · exact inProgram_of_textOffset 0x1907c (by decide)
    · exact inProgram_of_textOffset 0x19080 (by decide)
    · rw [topv]; exact chip)
  have fu : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - BitVec.ofNat 64 (529)) 1] v u := by
    simpa only [spv, BitVec.sub_sub, subOne] using eu.agrees
  have f : AgreesExcept (choiceClobbers s) t u := (fv.trans fu).mono (by simp [choiceClobbers])
  have spu : stackPtr u = stackPtr t := eu.rsp.trans (callEffect_stack ev').2
  have writes : WritesWithin (choiceClobbers s) #v[workRegion s] := by
    intro c hc a ha
    simp only [choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s,by simp,work_contains hs (by decide) (by decide) ha⟩
  refine ⟨u,hv.trans hu,state.after_effect call (hv.trans hu) ru f writes (spu.trans state.rsp)
    (by simp [choiceClobbers]),eu.rip.trans topv,?_,f⟩
  change (Operand.reg 0 : Operand 64).read u = _
  rw [eu.rax,fv.read (by simp)]


theorem choice_memory [Bindings] {initial : RamState} {secret message : ByteArray}
    (hc : ValidCall signingKeyTrySign initial [secret,message])
    {off len : Nat} (bound : off ≤ 520) (extent : len ≤ off+8) :
    ∀ a n, Component.mem a n ∈ choiceClobbers initial →
      RangeApart a n (stackPtr initial-BitVec.ofNat 64 off) len := by
  obtain ⟨slices,call⟩ := hc
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  intro a n member
  simp only [choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h
  all_goals cases h
  · exact stack_sub_apart hs (a:=528) (b:=off) (by omega) (by omega)
      (by omega) extent (.inl (by omega))
  · exact stack_sub_apart hs (a:=529) (b:=off) (by omega) (by omega)
      (by omega) extent (.inl (by omega))

end P256.Proofs.Signing.Wrapper.Entry.Decode
