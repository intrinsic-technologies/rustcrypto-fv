import Sha3.Proofs.Wrapper.Finish.Arguments
import Sha3.Proofs.Wrapper.Setup.Prefix

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def fullCopyPrefixPC (mode : Mode) : BitVec 64 := callAddress mode .sha256 true true + 5

def fullCopyTargetReg (mode : Mode) : BitVec 5 := if mode = .digest then 12 else 3

theorem full_copy_prefix [bindings : Bindings] {mode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPrefixPC mode)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (htemp : s.regValue .r14 = frameBase initial .sha256 mode true true +
      (if mode = .digest then 408 else 416 : BitVec 64)) :
    ∃ t, Advances (returnBoundary initial) 5 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = (if mode = .digest then 0x1020b0 else 0x10240e) ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      t.regValue .r15 = frameBase initial .sha256 mode true true +
        (if mode = .digest then 208 else 216 : BitVec 64) ∧
      (Operand.reg (fullCopyTargetReg mode) : Operand 64).read t = 0x106a70 ∧
      t.regValue .rdx = 200 ∧ t.regValue .rdi = t.regValue .r15 ∧
      t.regValue .rsi = frameBase initial .sha256 mode true true +
        (if mode = .digest then 408 else 416 : BitVec 64) ∧
      AgreesExcept [.reg 15, .reg (fullCopyTargetReg mode), .reg 2, .reg 7, .reg 6, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨a, ha, ia, spa, ea, aa⟩ := Reset.advanceNoMemory hCall
    (lea_r64_effect_step (fullCopyPrefixPC mode) 0x4c
      (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d32 (if mode = .digest then 208 else 216)))
      (by rcases hm with rfl | rfl <;> decide)
      (by rcases hm with rfl | rfl <;> decide)
      (by rcases hm with rfl | rfl <;> decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 15, .rip]) (by simp only [leaR64Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) inv hsp hp
  have pa : a.RIP = fullCopyPrefixPC mode + (8 : BitVec 64) := by
    rcases hm with rfl | rfl <;> exact ea.rip
  obtain ⟨b, hb, ib, spb, eb, ab⟩ := Reset.advanceNoMemory hCall
    (lea_r64_effect_step (fullCopyPrefixPC mode + 8) (if mode = .digest then 0x4c else 0x48)
      (by rcases hm with rfl | rfl <;> unfold RexWPrefix <;> decide)
      (if mode = .digest then 4 else 3)
      (.rip (if mode = .digest then 0x49cb else 0x466d)) (by trivial)
      (by rcases hm with rfl | rfl <;> decide)
      (by rcases hm with rfl | rfl <;> decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg (fullCopyTargetReg mode), .rip]) (noDf := by simp)
    (by rcases hm with rfl | rfl <;> simp only [leaR64Effect_components] <;> decide)
    (by simp [Component.Covers]) (by rcases hm with rfl | rfl <;> decide) ia spa pa
  have pb : b.RIP = fullCopyPrefixPC mode + (15 : BitVec 64) := by
    rcases hm with rfl | rfl <;> exact eb.rip
  obtain ⟨c, hc, ic, spc, ec, ac⟩ := Reset.advanceNoMemory hCall
    (mov_r32_imm32_effect_step (fullCopyPrefixPC mode + 15) 0xba (by decide) 200)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 2, .rip]) (by simp only [movR32Imm32Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ib spb pb
  have pc : c.RIP = fullCopyPrefixPC mode + (20 : BitVec 64) := by
    simpa only [movR32Imm32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using ec.rip
  obtain ⟨d, hd, id, spd, ed, ad⟩ := Reset.advanceNoMemory hCall
    (mov_r64_r64_effect_step (fullCopyPrefixPC mode + 20) 0x4c 0xff
      (by unfold RexWPrefix; decide) (by decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 7, .rip]) (by simp only [movR64R64Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ic spc pc
  have pd : d.RIP = fullCopyPrefixPC mode + (23 : BitVec 64) := by
    simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using ed.rip
  obtain ⟨t, ht, it, _, et, agt⟩ := Reset.advanceNoMemory hCall
    (mov_r64_r64_effect_step (fullCopyPrefixPC mode + 23) 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 6, .rip]) (by simp only [movR64R64Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) id spd pd
  have ag : AgreesExcept
      [.reg 15, .reg (fullCopyTargetReg mode), .reg 2, .reg 7, .reg 6, .rip] s t :=
    (aa.trans (ab.trans (ac.trans (ad.trans agt)))).mono (by simp)
  have r15 : t.regValue .r15 = a.regValue .r15 :=
    (agt.read (r := 15) (n := 64) (by decide)).trans
      ((ad.read (r := 15) (n := 64) (by decide)).trans
        ((ac.read (r := 15) (n := 64) (by decide)).trans
          (ab.read (r := 15) (n := 64) (by rcases hm with rfl | rfl <;> decide))))
  refine ⟨t, ha.trans (hb.trans (hc.trans (hd.trans ht))), it, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ag⟩
  · rcases hm with rfl | rfl <;> exact et.rip
  · exact (ag.read (r := 4) (n := 64) (by rcases hm with rfl | rfl <;> decide)).trans hs
  · rw [r15]
    have h := ea.writes
    change a.regValue .r15 = _ at h
    rcases hm with rfl | rfl <;> exact h.trans (congrArg (fun p : BitVec 64 ↦ p + _) hs)
  · have keep := (agt.read (r := fullCopyTargetReg mode) (n := 64)
        (by rcases hm with rfl | rfl <;> decide)).trans
      ((ad.read (r := fullCopyTargetReg mode) (n := 64)
        (by rcases hm with rfl | rfl <;> decide)).trans
        (ac.read (r := fullCopyTargetReg mode) (n := 64)
          (by rcases hm with rfl | rfl <;> decide)))
    rw [keep]
    rcases hm with rfl | rfl <;> exact eb.writes
  · exact (agt.read (r := 2) (n := 64) (by decide)).trans
      ((ad.read (r := 2) (n := 64) (by decide)).trans ec.writes)
  · have h : d.regValue .rdi = c.regValue .r15 := ed.writes
    exact (agt.read (r := 7) (n := 64) (by decide)).trans
      (h.trans ((ad.read (r := 15) (n := 64) (by decide)).symm.trans
        (agt.read (r := 15) (n := 64) (by decide)).symm))
  · have h : t.regValue .rsi = d.regValue .r14 := et.writes
    exact h.trans (((aa.trans (ab.trans (ac.trans ad))).read (r := 14) (n := 64)
      (by rcases hm with rfl | rfl <;> decide)).trans htemp)

def fullCopySuffixPC (mode : Mode) : BitVec 64 :=
  if mode = .digest then 0x1020b3 else 0x102410

theorem full_copy_suffix [bindings : Bindings] {mode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopySuffixPC mode)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hout : (outputOperand initial .sha256 mode true true).read s = out) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = (if mode = .digest then 0x1020be else 0x10241c) ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      t.regValue .rdi = out ∧ t.regValue .rsi = s.regValue .r15 ∧
      t.regValue .rdx = 200 ∧ AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨a, ha, ia, spa, ea, aa⟩ := Reset.advanceNoMemory hCall
    (mov_r32_imm32_effect_step (fullCopySuffixPC mode) 0xba (by decide) 200)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 2, .rip]) (by simp only [movR32Imm32Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) inv hsp hp
  have pa : a.RIP = fullCopySuffixPC mode + (5 : BitVec 64) := ea.rip
  have spa' : stackPtr a = frameBase initial .sha256 mode true true :=
    (aa.read (r := 4) (n := 64) (by decide)).trans hs
  have outa : (outputOperand initial .sha256 mode true true).read a = out := by
    rcases hm with rfl | rfl
    · have mem := aa.external (by simp [Component.Covers])
      simpa only [outputOperand, Operand.read, mem] using hout
    · exact (aa.read (r := 3) (n := 64) (by decide)).trans hout
  have middle : ∃ b, Advances (returnBoundary initial) 1 a b ∧
      Invariant initial .sha256 mode b true true ∧
      b.GPR[4] ≠ (returnBoundary initial).rsp ∧
      b.RIP = fullCopySuffixPC mode + (if mode = .digest then 8 else 9 : BitVec 64) ∧
      b.regValue .rdi = out ∧ AgreesExcept [.reg 7, .rip] a b := by
    rcases hm with rfl | rfl
    · have hread : MemReadable a (stackPtr a) 8 := by
        rw [spa']
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          ia.frameReadable hCall.stackAvailable (offset := 0) (count := 8) (by decide)
      obtain ⟨b, hb, ib, spb, eb, ab⟩ := Reset.advanceNoMemory hCall
        (mov_r64_m64_effect_step (fullCopySuffixPC .plain + 5) 0x48
          (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 .none)
          (by decide) (by decide) (by decide))
        (by unfold ImageAt; decide +kernel)
        (changes := [.reg 7, .rip]) (by simp only [movR64M64Effect_components]; decide)
        (by simp [Component.Covers]) (by decide) ia spa ⟨pa, by
          change MemReadable a (stackPtr a + 0) 8
          rw [show stackPtr a + 0 = stackPtr a from BitVec.add_zero _]
          exact hread⟩
      refine ⟨b, hb, ib, spb, eb.rip, ?_, ab⟩
      have h := eb.writes
      change b.regValue .rdi = (Operand.mem (stackPtr a + 0) : Operand 64).read a at h
      rw [show stackPtr a + 0 = stackPtr a from BitVec.add_zero _, spa'] at h
      apply h.trans
      simpa only [outputOperand, outputSlot, Mode.outputSlotOffset, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero] using outa
    · obtain ⟨b, hb, ib, spb, eb, ab⟩ := Reset.advanceNoMemory hCall
        (mov_r64_r64_effect_step (fullCopySuffixPC .digest + 5) 0x48 0xdf
          (by unfold RexWPrefix; decide) (by decide))
        (by unfold ImageAt; decide +kernel)
        (changes := [.reg 7, .rip]) (by simp only [movR64R64Effect_components]; decide)
        (by simp [Component.Covers]) (by decide) ia spa pa
      exact ⟨b, hb, ib, spb, eb.rip, eb.writes.trans outa, ab⟩
  obtain ⟨b, hb, ib, spb, pb, rb, ab⟩ := middle
  obtain ⟨t, ht, it, _, et, agt⟩ := Reset.advanceNoMemory hCall
    (mov_r64_r64_effect_step
      (fullCopySuffixPC mode + (if mode = .digest then 8 else 9 : BitVec 64)) 0x4c 0xfe
      (by unfold RexWPrefix; decide) (by decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 6, .rip]) (by simp only [movR64R64Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ib spb pb
  have ag : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t :=
    (aa.trans (ab.trans agt)).mono (by simp)
  refine ⟨t, ha.trans (hb.trans ht), it, ?_, ?_, ?_, ?_, ?_, ag⟩
  · rcases hm with rfl | rfl <;> exact et.rip
  · exact (ag.read (r := 4) (n := 64) (by decide)).trans hs
  · exact (agt.read (r := 7) (n := 64) (by decide)).trans rb
  · have h : t.regValue .rsi = b.regValue .r15 := et.writes
    exact h.trans ((aa.trans ab).read (r := 15) (n := 64) (by decide))
  · exact (agt.read (r := 2) (n := 64) (by decide)).trans
      ((ab.read (r := 2) (n := 64) (by decide)).trans ea.writes)

end Sha3.Proofs.Wrapper.Finish.Plain
