import P256.Proofs.Program.Copy.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.Copy

theorem finish [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {reserve fuel : Nat}
    (bindingsSupported : MachineRamUnitStrideDecodable bindings s)
    (machine : SupportedIntegerMachineState bindings.processor s) (loaded : ProgramLoaded s)
    (direction : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (stack : MemReadable s (stackPtr s) 8)
    (low : (returnBoundary s).rip.toNat < 2^32)
    (returnNe : (returnBoundary s).rip ≠ boundary.rip)
    (ready : ReadyToStep t) (agrees : AgreesExcept registerComponents s t)
    (rip : t.RIP = 0x11c95e) (execution : Advances boundary fuel s t) :
    ∃ final, CalleeResult s final boundary 0 reserve ∧
      AgreesExcept (registerComponents ++ [.reg 4, .rip]) s final ∧
      final.external = s.external := by
  have memory : t.external = s.external := agrees.external (by simp [registerComponents, Component.Covers])
  have rsp : stackPtr t = stackPtr s := agrees.read (n := 64) (r := 4) (by simp [registerComponents])
  have top : stackTop t = (returnBoundary s).rip := by
    change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
    rw [memory, rsp]
  have code := agrees.codeIn (by simp [registerComponents, Component.Covers]) (programLoaded_codeIn loaded)
  have readable : MemReadable t (stackPtr t) 8 := by
    rw [rsp]
    exact ⟨stack.low, by simpa only [memory] using stack.mem⟩
  obtain ⟨final, run, finalReady, effect⟩ := (ret_effect_step 0x11c95e).advances ready
    (programText_slice code 0x1c95e _ (by decide) (by decide +kernel))
    ⟨⟨rip, readable⟩, top ▸ low⟩ (by change stackTop t ≠ boundary.rip; rw [top]; exact returnNe)
  have full : AgreesExcept (registerComponents ++ [.reg 4, .rip]) s final := agrees.trans effect.agrees
  have finalMemory : final.external = s.external := full.external
    (by simp [registerComponents, Component.Covers])
  refine ⟨final, ⟨⟨fuel+1, execution.trans run⟩, effect.rip.trans top, ?_,
    bindingsSupported_of_ready_agrees bindingsSupported finalReady full,
    supportedMachine_of_ready_agrees machine finalReady full, ?_,
    full.directionFlagClear (by simp [registerComponents]) direction,
    full.mxcsr (by simp [registerComponents]), full.fcw (by simp [registerComponents]), ?_, ?_, full.grow⟩, full, finalMemory⟩
  · have value : final.regValue .rsp = stackPtr t + 8 := effect.writes
    rw [value, rsp]
    rfl
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact full.read (n := 64) (r := 3) (by simp [registerComponents])
    · exact full.read (n := 64) (r := 5) (by simp [registerComponents])
    · exact full.read (n := 64) (r := 12) (by simp [registerComponents])
    · exact full.read (n := 64) (r := 13) (by simp [registerComponents])
    · exact full.read (n := 64) (r := 14) (by simp [registerComponents])
    · exact full.read (n := 64) (r := 15) (by simp [registerComponents])
  · intro a _
    rw [finalMemory]
  · intro a byte h
    rw [finalMemory]
    exact loaded a byte h

end P256.Proofs.Nonce.Update.Absorb.Seeded.Zero
