import P256.Proofs.Signing.Wrapper.Entry.Decode.Prepare
import P256.Proofs.Signing.Wrapper.Entry.Decode.Memory
import P256.Proofs.Signing.Wrapper.Entry.Decode.Zero
import P256.Proofs.Signing.Wrapper.Entry.Decode.Arguments

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure ReadEntry [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520 where
  rip : s.RIP = 0x102461
  source : s.regValue .rdi = stackPtr initial-184
  destination : s.regValue .rdx = stackPtr initial-520
  count : s.regValue .rsi = 32
  limbs : s.regValue .rcx = 4
  bits : s.regValue .r8 = 256
  bytes : (MemoryRegion.mk (stackPtr initial-184).toNat 32).HasBytes s.external secret
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r15 = initial.regValue .rdx
  inputCount : s.regValue .r13 = 2
  output : s.regValue .rbx = initial.regValue .rcx
  capacity : s.regValue .r14 = initial.regValue .r8

theorem read_entry [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (entry : GuardedEntry initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadEntry initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨n,a,ha,sa,ipa,pa,la,ca,ba,oa,qa⟩ := prepare context call entry
  obtain ⟨m,b,hb,rb,_,eb⟩ := zero_correct (returnBoundary initial) outside a
    (readyToStep sa.machine sa.bindingsSupported)
    (programText_slice (programLoaded_codeIn sa.loaded) 0x2418 zeroBytes
      (by decide) (by decide +kernel))
    (block_pre call sa ipa (by simp) (by simp))
  have sb : State initial b 520 := sa.after_effect call hb rb eb.agrees
    (by
      intro c hc x hx
      simp only [zeroEffect,Effect.components,Write.component,Operand.component,
        List.map_cons,List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact hx.elim
      all_goals exact ⟨workRegion initial,by simp,stack_work call sa (by decide) hx⟩)
    ((eb.agrees.read (n:=64) (r:=4) (by simp [zeroEffect,Effect.components])).trans sa.rsp)
    (by simp [zeroEffect,Effect.components])
  have bb : (MemoryRegion.mk (stackPtr initial-184).toNat 32).HasBytes b.external secret := by
    apply hasBytes_agrees_apart eb.agrees
    · intro addr len member
      simp only [zeroEffect,Effect.components,Write.component,Operand.component,
        List.map_cons,List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
      have src : stackPtr initial-184 = stackPtr a+336 := by
        symm
        exact stack_address sa (by decide)
      rw [src]
      rcases member with (h | h | h | h | h) | h
      all_goals try cases h
      all_goals intro i hi j hj he
      all_goals exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) (stackPtr a) hi hj (by decide) he
    · exact ba
  obtain ⟨k,t,ht,rt,_,et⟩ := decoder_arguments (returnBoundary initial) outside b
    (readyToStep sb.machine sb.bindingsSupported)
    (programText_slice (programLoaded_codeIn sb.loaded) 0x2446 decoderArgumentBytes
      (by decide) (by decide +kernel)) eb.rip
  have st : State initial t 520 := sb.after_effect call ht rt et.agrees
    (by simp [decoderArgumentEffect,Effect.components,WritesWithin,Component.Covers])
    ((et.agrees.read (n:=64) (r:=4) (by simp [decoderArgumentEffect,Effect.components])).trans sb.rsp)
    (by simp [decoderArgumentEffect,Effect.components])
  have ag := eb.agrees.trans et.agrees
  refine ⟨n+m+k,t,(ha.trans hb).trans ht,⟨st,et.rip,?_,?_,et.writes.2.2.1,
    et.writes.2.2.2.1,et.writes.2.2.2.2,?_,?_,?_,?_,?_,?_⟩⟩
  · exact et.writes.1.trans (stack_address sb (by decide))
  · exact et.writes.2.1.trans sb.rsp
  · simpa only [et.agrees.external (by simp [decoderArgumentEffect,Effect.components,
      Component.Covers])] using bb
  · exact (ag.read (n:=64) (r:=12) (by simp [zeroEffect,decoderArgumentEffect,
      Effect.components])).trans pa
  · exact (ag.read (n:=64) (r:=15) (by simp [zeroEffect,decoderArgumentEffect,
      Effect.components])).trans la
  · exact (ag.read (n:=64) (r:=13) (by simp [zeroEffect,decoderArgumentEffect,
      Effect.components])).trans ca
  · exact (ag.read (n:=64) (r:=3) (by simp [zeroEffect,decoderArgumentEffect,
      Effect.components])).trans oa
  · exact (ag.read (n:=64) (r:=14) (by simp [zeroEffect,decoderArgumentEffect,
      Effect.components])).trans qa

end P256.Proofs.Signing.Wrapper.Entry.Decode
