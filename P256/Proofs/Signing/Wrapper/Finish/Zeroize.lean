import P256.Proofs.Signing.Wrapper.Finish.Stack

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem zeroize [Bindings] {initial s : RamState} (pre : Pre initial) (state : State initial s)
    (rip : s.RIP = 0x102ab8) :
    ∃ t, Advances (returnBoundary initial) 12 s t ∧ State initial t ∧
      t.RIP = 0x102b10 ∧ t.regValue .r11 = s.regValue .r11 ∧ MemoryWriteFrame s t #v[Stack.region initial 5112] := by
  obtain ⟨s1,run1,st1,ip1,out1,frame1⟩ :=
    store_stack pre state 0x2ab8 true (.d8 64) 456
      rfl (by decide) (by decide) (by decide) (by decide) rip (by decide +kernel) (by decide)
  obtain ⟨s2,run2,st2,ip2,out2,frame2⟩ :=
    store_stack pre st1 0x2ac1 true (.d8 72) 448
      rfl (by decide) (by decide) (by decide) (by decide) ip1 (by decide +kernel) (by decide)
  obtain ⟨s3,run3,st3,ip3,out3,frame3⟩ :=
    store_stack pre st2 0x2aca true (.d8 80) 440
      rfl (by decide) (by decide) (by decide) (by decide) ip2 (by decide +kernel) (by decide)
  obtain ⟨s4,run4,st4,ip4,out4,frame4⟩ :=
    store_stack pre st3 0x2ad3 true (.d8 88) 432
      rfl (by decide) (by decide) (by decide) (by decide) ip3 (by decide +kernel) (by decide)
  obtain ⟨s5,run5,st5,ip5,out5,frame5⟩ :=
    load_stack pre st4 0x2adc (.d8 64) 64 rfl (by decide) ip4 (by decide +kernel) (by decide)
  obtain ⟨s6,run6,st6,ip6,out6,frame6⟩ :=
    store_stack pre st5 0x2ae1 false (.d32 368) 152
      rfl (by decide) (by decide) (by decide) (by decide) ip5 (by decide +kernel) (by decide)
  obtain ⟨s7,run7,st7,ip7,out7,frame7⟩ :=
    load_stack pre st6 0x2ae9 (.d8 72) 72 rfl (by decide) ip6 (by decide +kernel) (by decide)
  obtain ⟨s8,run8,st8,ip8,out8,frame8⟩ :=
    store_stack pre st7 0x2aee false (.d32 376) 144
      rfl (by decide) (by decide) (by decide) (by decide) ip7 (by decide +kernel) (by decide)
  obtain ⟨s9,run9,st9,ip9,out9,frame9⟩ :=
    load_stack pre st8 0x2af6 (.d8 80) 80 rfl (by decide) ip8 (by decide +kernel) (by decide)
  obtain ⟨s10,run10,st10,ip10,out10,frame10⟩ :=
    store_stack pre st9 0x2afb false (.d32 384) 136
      rfl (by decide) (by decide) (by decide) (by decide) ip9 (by decide +kernel) (by decide)
  obtain ⟨s11,run11,st11,ip11,out11,frame11⟩ :=
    load_stack pre st10 0x2b03 (.d8 88) 88 rfl (by decide) ip10 (by decide +kernel) (by decide)
  obtain ⟨s12,run12,st12,ip12,out12,frame12⟩ :=
    store_stack pre st11 0x2b08 false (.d32 392) 128
      rfl (by decide) (by decide) (by decide) (by decide) ip11 (by decide +kernel) (by decide)
  exact ⟨s12,(((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12),st12,ip12,out12.trans (out11.trans (out10.trans (out9.trans (out8.trans (out7.trans (out6.trans (out5.trans (out4.trans (out3.trans (out2.trans (out1))))))))))),(memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans frame1 frame2) frame3) frame4) frame5) frame6) frame7) frame8) frame9) frame10) frame11) frame12)⟩

end P256.Proofs.Signing.Wrapper.Finish
