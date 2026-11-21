import P256.Proofs.EcdhWrapper.Scalar.Call
import P256.Proofs.SecretKeyFromBytes.Choice
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem choice_at [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (offset : Nat) (disp : BitVec 32) (bound : offset+5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : s.RIP = Extracted.textAddress+BitVec.ofNat 64 offset) (rsp : stackPtr s = stackPtr initial-504) :
    ∃ u, Advances (returnBoundary initial) 6 s u ∧ ReadyToStep u ∧
      u.RIP = Extracted.textAddress+BitVec.ofNat 64 offset+5#64 ∧ stackPtr u = stackPtr s ∧
      u.regValue .rax = ((s.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept [.reg 0,.reg 4,.flags,.rip,
        .mem (stackPtr initial-512) 8,.mem (stackPtr initial-513) 1] s u := by
  obtain ⟨t,run,rt,lt,e,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside ready loaded grow 504 offset disp rsp rip
    (by decide) (by decide) (by omega) bytes
    (by rw [target]; exact inProgram_of_textOffset 0x19070 (by decide))
  have nextIn : InProgram (Extracted.textAddress+BitVec.ofNat 64 offset+5#64) := by
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
      inProgram_of_textOffset (offset+5) bound
  have push : pushAddr s = stackPtr initial-512 := by
    rw [pushAddr,rsp,BitVec.sub_sub]; rfl
  have st : stackPtr t = stackPtr initial-512 := e.writes.1.trans push
  have top : stackTop t = Extracted.textAddress+BitVec.ofNat 64 offset+5#64 := (callEffect_stack e).1
  have ag : AgreesExcept [.reg 4,.mem (stackPtr initial-512) 8,.rip] s t := by
    simpa only [pushEffect_components,push] using e.agrees
  have sub : stackPtr t-1 = stackPtr initial-513 := by rw [st,BitVec.sub_sub]; rfl
  have cp : SecretKeyFromBytes.ChoicePre t := by
    refine ⟨e.rip.trans target,?_,?_,?_,?_⟩
    · rw [sub]
      exact writable_of_grow (stack_sub_writable call.stackAvailable.1
        (fun a ha hp => call_stack_avoids call a ha (.inr hp))
        (offset := 513) (len := 1) (by decide) (by decide) (by decide)
        (by have h := Nat.mod_lt (stackPtr initial-513).toNat (by decide : 0<4096); omega))
        (fun a ha => ag.grow a (grow a ha))
    · rw [st]
      exact readable_of_grow (stack_sub_readable call.stackAvailable.1
        (offset := 512) (len := 8) (by decide) (by decide)) (fun a ha => ag.grow a (grow a ha))
    · rw [top]; exact inProgram_low nextIn
    · rw [sub]
      exact stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
        (offset := 513) (len := 1) (by decide) (by decide)
        (codeOffset := 0x19070) (codeLength := 17) (by decide)
  obtain ⟨u,ru,readyU,eu⟩ := SecretKeyFromBytes.choice_correct rt
    (SecretKeyFromBytes.choice_code_loaded lt) cp (by
      intro q hq
      apply boundary_ne_program outside
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact inProgram_of_textOffset 0x19074 (by decide)
      · exact inProgram_of_textOffset 0x19078 (by decide)
      · exact inProgram_of_textOffset 0x1907c (by decide)
      · exact inProgram_of_textOffset 0x19080 (by decide)
      · rw [top]
        exact nextIn)
  have gu : AgreesExcept [.reg 0,.reg 4,.flags,.rip,.mem (stackPtr initial-513) 1] t u := by
    simpa only [sub] using eu.agrees
  refine ⟨u,run.trans ru,readyU,eu.rip.trans top,
    eu.rsp.trans (callEffect_stack e).2,?_,(ag.trans gu).mono (by simp)⟩
  change (Operand.reg 0 : Operand 64).read u = _
  rw [eu.rax,ag.read (by simp)]
  rfl

theorem choice [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x10691e) (rsp : stackPtr s = stackPtr initial-504) :
    ∃ u, Advances (returnBoundary initial) 6 s u ∧ ReadyToStep u ∧
      u.RIP = 0x106923 ∧ stackPtr u = stackPtr s ∧
      u.regValue .rax = ((s.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept [.reg 0,.reg 4,.flags,.rip,
        .mem (stackPtr initial-512) 8,.mem (stackPtr initial-513) 1] s u := by
  exact choice_at call outside ready loaded grow 0x691e 0x1274d
    (by decide) (by decide +kernel) (by decide) rip rsp

end P256.Proofs.EcdhWrapper.Nonzero
