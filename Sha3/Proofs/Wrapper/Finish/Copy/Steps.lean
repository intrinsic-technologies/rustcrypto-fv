import Sha3.Proofs.Wrapper.Reset.Selection
import Sha3.Proofs.Wrapper.Finish.Copy.Layout

namespace Sha3.Proofs.Wrapper.Finish.Copy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def prefixChanges : List Component := [.reg 3, .reg 6, .reg 2, .reg 7, .rip]

theorem prefixImage (v : Variant) (mode : Mode := .finalizeReset)
    (keccak : Bool := false) (fullState : Bool := false)
    (hMode : mode.hasBeforeOutput = true := by decide) :
    ImageAt ((mode.entry v keccak fullState).entryAddress +
      BitVec.ofNat 64 (startOffset v mode keccak fullState)) (prefixBytes v mode fullState) := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
    first | contradiction | (unfold ImageAt; decide +kernel)

theorem prefixChanges_noMem : ∀ c ∈ prefixChanges, ∀ a, ¬ c.Covers a := by
  simp [prefixChanges, Component.Covers]

theorem prefix_steps [bindings : Bindings] {initial s : RamState} {v : Variant}
    {mode : Mode} {keccak fullState : Bool} {p base : BitVec 64} {destination source : Disp}
    {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState)
    (ip : s.RIP = p)
    (sp : stackPtr s = base)
    (image1 : ImageAt p (0x48 :: 0x8d :: (AddrMode.sib 4 none 0 destination).modrm 3 ::
      (AddrMode.sib 4 none 0 destination).tail))
    (image2 : ImageAt (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination)))
      (0x48 :: 0x8d :: (AddrMode.sib 4 none 0 source).modrm 6 ::
        (AddrMode.sib 4 none 0 source).tail))
    (image3 : ImageAt (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) +
      leaLen (.sib 4 none 0 source))) [0xba, 0xd0, 0, 0, 0])
    (image4 : ImageAt (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) +
      leaLen (.sib 4 none 0 source) + 5)) [0x48, 0x89, 0xdf])
    (inside : s.GPR[4] ≠ (returnBoundary initial).rsp) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source) + 8) ∧
      stackPtr t = base ∧
      (Operand.reg 3 : Operand 64).read t = base + destination.value ∧
      (Operand.reg 7 : Operand 64).read t = base + destination.value ∧
      (Operand.reg 6 : Operand 64).read t = base + source.value ∧
      (Operand.reg 2 : Operand 64).read t = 208 ∧
      AgreesExcept prefixChanges s t := by
  obtain ⟨a, h1, i1, sp1, e1, a1⟩ := Reset.advanceNoMemory
    (effect := leaR64Effect p 3 (.sib 4 none 0 destination)) hCall
    (lea_r64_effect_step p 0x48 (by unfold RexWPrefix; decide) 3
      (.sib 4 none 0 destination) (by simp [AddrMode.Valid, regLow]) (by rfl) (by rfl))
    image1
    (by simp [prefixChanges]) prefixChanges_noMem (by simp [prefixChanges]) inv inside ip
  have aRip : a.RIP = p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination)) := e1.rip
  obtain ⟨b, h2, i2, sp2, e2, a2⟩ := Reset.advanceNoMemory
    (effect := leaR64Effect (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination))) 6 (.sib 4 none 0 source)) hCall
    (lea_r64_effect_step (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination))) 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 source) (by simp [AddrMode.Valid, regLow]) (by rfl) (by rfl))
    image2
    (by simp [prefixChanges]) prefixChanges_noMem (by simp [prefixChanges]) i1 sp1 aRip
  have bRip : b.RIP = p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source)) := by
    simpa [leaR64Effect, BitVec.ofNat_add, BitVec.add_assoc] using e2.rip
  obtain ⟨c, h3, i3, sp3, e3, a3⟩ := Reset.advanceNoMemory
    (effect := movR32Imm32Effect (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source))) 5 2 208) hCall
    (mov_r32_imm32_effect_step (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source))) 0xba (by decide) 208)
    image3
    (by simp [prefixChanges]) prefixChanges_noMem (by simp [prefixChanges]) i2 sp2 bRip
  have cRip : c.RIP = p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source) + 5) := by
    simpa [movR32Imm32Effect, BitVec.ofNat_add, BitVec.add_assoc] using e3.rip
  obtain ⟨t, h4, i4, _, e4, a4⟩ := Reset.advanceNoMemory
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source) + 5)) 7 3) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (leaLen (.sib 4 none 0 destination) + leaLen (.sib 4 none 0 source) + 5)) 0x48 0xdf (by unfold RexWPrefix; decide) (by decide))
    image4
    (by simp [prefixChanges]) prefixChanges_noMem (by simp [prefixChanges]) i3 sp3 cRip
  have agrees : AgreesExcept prefixChanges s t :=
    (a1.trans (a2.trans (a3.trans a4))).mono (by
      intro q hq
      simp only [List.mem_append] at hq
      rcases hq with hq | hq | hq | hq <;> exact hq)
  have arbx : (Operand.reg 3 : Operand 64).read a =
      base + destination.value := e1.writes.trans (congrArg (· + destination.value) sp)
  have crbx : (Operand.reg 3 : Operand 64).read c =
      base + destination.value :=
    (e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans arbx)
  have arsp : (Operand.reg 4 : Operand 64).read a = base :=
    (a1.read (by decide)).trans sp
  have brsi : (Operand.reg 6 : Operand 64).read b =
      base + source.value := e2.writes.trans (congrArg (· + source.value) arsp)
  refine ⟨t, h1.trans (h2.trans (h3.trans h4)), i4, ?_,
    (agrees.read (n := 64) (r := 4) (by decide)).trans sp,
    (e4.agrees.read (by simp)).trans crbx, e4.writes.trans crbx,
    (e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans brsi),
    (e4.agrees.read (by simp)).trans e3.writes, agrees⟩
  simpa [movR64R64Effect, BitVec.ofNat_add, BitVec.add_assoc] using e4.rip

theorem suffixImage (v : Variant) (mode : Mode := .finalizeReset)
    (keccak : Bool := false) (fullState : Bool := false)
    (hMode : mode.hasBeforeOutput = true := by decide) :
    ImageAt (callPC v mode keccak fullState + 6) (suffixBytes v mode fullState) := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
    first | contradiction | (unfold ImageAt; decide +kernel)

theorem suffix_steps [bindings : Bindings] {initial s : RamState} {v : Variant}
    {mode : Mode} {keccak fullState : Bool} {p base : BitVec 64}
    {destination : BitVec 64} {outputSlot : BitVec 8}
    {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState)
    (ip : s.RIP = p)
    (sp : stackPtr s = base)
    (rbx : (Operand.reg 3 : Operand 64).read s = base + destination)
    (slot : (Operand.mem (base + outputSlot.signExtend 64) : Operand 64).read s = out)
    (image1 : ImageAt p [0x48, 0x89, 0xdf])
    (image2 : ImageAt (p + 3) (0x48 :: 0x8b ::
      (AddrMode.sib 4 none 0 (.d8 outputSlot)).modrm 6 ::
      (AddrMode.sib 4 none 0 (.d8 outputSlot)).tail))
    (readable : MemReadable s (base + outputSlot.signExtend 64) 8)
    (inside : s.GPR[4] ≠ (returnBoundary initial).rsp) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + (8 : BitVec 64) ∧
      stackPtr t = base ∧
      (Operand.reg 7 : Operand 64).read t = base + destination ∧
      (Operand.reg 6 : Operand 64).read t = out ∧ AgreesExcept prefixChanges s t := by
  obtain ⟨a, h1, i1, sp1, e1, a1⟩ := Reset.advanceNoMemory
    (effect := movR64R64Effect p 7 3) hCall
    (mov_r64_r64_effect_step p 0x48 0xdf (by unfold RexWPrefix; decide) (by decide))
    image1
    (by simp [prefixChanges]) prefixChanges_noMem (by simp [prefixChanges]) inv inside ip
  have asp : stackPtr a = base :=
    (a1.read (n := 64) (r := 4) (by decide)).trans sp
  have amem : a.external = s.external := a1.external prefixChanges_noMem
  have hread : MemReadable a
      ((AddrMode.sib 4 none 0 (.d8 outputSlot)).addr a (p + 3 + 5)) 8 := by
    change MemReadable a (stackPtr a + outputSlot.signExtend 64) 8
    rw [asp]
    exact readable.of_external_eq amem
  obtain ⟨t, h2, i2, _, e2, a2⟩ := Reset.advanceNoMemory
    (effect := movR64M64Effect (p + 3) 6 (.sib 4 none 0 (.d8 outputSlot))) hCall
    (mov_r64_m64_effect_step (p + 3) 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 outputSlot)) (by simp [AddrMode.Valid, regLow]) (by rfl) (by rfl))
    image2
    (by simp [prefixChanges]) prefixChanges_noMem (by simp [prefixChanges]) i1 sp1
    ⟨e1.rip, hread⟩
  have agrees : AgreesExcept prefixChanges s t :=
    (a1.trans a2).mono (by intro q hq; exact (List.mem_append.mp hq).elim id id)
  refine ⟨t, h1.trans h2, i2, ?_,
    (agrees.read (n := 64) (r := 4) (by decide)).trans sp,
    (e2.agrees.read (by simp)).trans (e1.writes.trans rbx), ?_, agrees⟩
  · simpa [movR64M64Effect, movLoadLen, AddrMode.tail, Disp.bytes, immBytes,
      BitVec.add_assoc] using e2.rip
  · have hh : (Operand.reg 6 : Operand 64).read t =
        (Operand.mem (stackPtr a + outputSlot.signExtend 64) : Operand 64).read a := e2.writes
    rw [hh, asp]
    change memLoad a.external _ 64 = _
    rw [amem]
    exact slot

end Sha3.Proofs.Wrapper.Finish.Copy
