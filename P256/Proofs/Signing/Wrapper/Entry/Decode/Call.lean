import P256.Proofs.Signing.Wrapper.Entry.Decode.ReadBe

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure CalleeEntry [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 528 where
  pre : ReadBe.Pre s (returnBoundary initial)
  bytes : (registerRegion s .rdi 32).HasBytes s.external secret
  destination : s.regValue .rdx = stackPtr initial-520
  decoderReturn : (returnBoundary s).rip = 0x102466
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r15 = initial.regValue .rdx
  count : s.regValue .r13 = 2
  output : s.regValue .rbx = initial.regValue .rcx
  capacity : s.regValue .r14 = initial.regValue .r8

theorem enter_decoder [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (entry : GuardedEntry initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ CalleeEntry initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨n,a,ha,sa⟩ := read_entry context entry
  obtain ⟨t,ht,rt,_,et,_⟩ := call_rel32_exists hs
    (by simpa only [signingKeyTrySign] using call_stack_avoids call) outside (readyToStep sa.machine sa.bindingsSupported)
    sa.loaded sa.allocated 520 0x2461 0x16c2a sa.rsp sa.rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x19090 (by decide))
  have push : pushAddr a = stackPtr initial-528 := by
    rw [pushAddr,sa.rsp,BitVec.sub_sub]
    rfl
  have ag : AgreesExcept [.reg 4,.mem (stackPtr initial-528) 8,.rip] a t := by
    simpa only [pushEffect_components,push] using et.agrees
  have st : State initial t 528 := sa.toState.after_effect call ht rt ag
    (by
      intro c hc x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hx.elim
      · exact ⟨workRegion initial,by simp,work_contains hs (offset:=528) (by decide) (by decide) hx⟩
      · exact hx.elim)
    (et.writes.1.trans push) (by simp)
  have et' : (callEffect (fun _ => 0x119090) 0x102466 a).Holds a t := et
  have pre := readBe_pre context.call context.bindingsSupported context.machine sa rt st.loaded et'
  refine ⟨n+1,t,ha.trans ht,⟨st,pre,?_,?_,(callEffect_stack et').1,?_,?_,?_,?_,?_⟩⟩
  · have src : t.regValue .rdi = stackPtr initial-184 :=
      (ag.read (n:=64) (r:=7) (by simp)).trans sa.source
    change (MemoryRegion.mk (t.regValue .rdi).toNat 32).HasBytes t.external secret
    rw [src]
    apply hasBytes_agrees_apart ag
    · intro addr len member
      have h : addr = stackPtr initial-528 ∧ len = 8 := by simpa using member
      obtain ⟨rfl,rfl⟩ := h
      exact stack_sub_apart hs (a:=528) (b:=184)
        (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
    · exact sa.bytes
  · exact (ag.read (n:=64) (r:=2) (by simp)).trans sa.destination
  · exact (ag.read (n:=64) (r:=12) (by simp)).trans sa.pointers
  · exact (ag.read (n:=64) (r:=15) (by simp)).trans sa.lengths
  · exact (ag.read (n:=64) (r:=13) (by simp)).trans sa.inputCount
  · exact (ag.read (n:=64) (r:=3) (by simp)).trans sa.output
  · exact (ag.read (n:=64) (r:=14) (by simp)).trans sa.capacity

end P256.Proofs.Signing.Wrapper.Entry.Decode
