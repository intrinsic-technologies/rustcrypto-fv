import Sha3.Proofs.Wrapper.Finish.Arguments
import Sha3.Proofs.Wrapper.Setup.Prefix
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Wrapper.Finish.FinalizeCall
import Sha3.Proofs.Finalize
import Sha3.Proofs.Wrapper.Finish.Plain.Call
import Sha3.Proofs.Wrapper.Finish.Plain.Full.Copy

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def fullTempOffset (mode : Mode) : Nat := if mode = .digest then 408 else 416

theorem full_temp_image (mode : Mode) (hm : mode = .plain ∨ mode = .digest) :
    ImageAt (startAddress mode .sha256 true true)
      (encodeLeaR64M 14 (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (fullTempOffset mode))))) := by
  rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel

theorem full_temp_advance [bindings : Bindings] {mode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true)
    (hs : stackPtr s = frameBase initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = startAddress mode .sha256 true true + (8 : BitVec 64) ∧
      t.regValue .r14 = frameBase initial .sha256 mode true true +
        BitVec.ofNat 64 (fullTempOffset mode) ∧
      AgreesExcept [.reg 14, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  have himage := full_temp_image mode hm
  have heq : encodeLeaR64M 14 (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (fullTempOffset mode)))) =
      0x4c :: 0x8d :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (fullTempOffset mode)))).modrm 14 ::
        (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (fullTempOffset mode)))).tail := by
    rcases hm with rfl | rfl <;> rfl
  rw [heq] at himage
  obtain ⟨t, ht, it, _, et, ag⟩ := Reset.advanceNoMemory hCall
    (lea_r64_effect_step (startAddress mode .sha256 true true) 0x4c
      (by unfold RexWPrefix; decide +kernel) 14
      (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (fullTempOffset mode))))
      (by rcases hm with rfl | rfl <;> decide +kernel)
      (by rcases hm with rfl | rfl <;> decide +kernel)
      (by rcases hm with rfl | rfl <;> decide +kernel))
    himage (changes := [.reg 14, .rip]) (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [Component.Covers]) (by decide +kernel) inv hsp hp
  refine ⟨t, ht, it, ?_, ?_, ag⟩
  · rcases hm with rfl | rfl <;> exact et.rip
  · have h := et.writes
    change t.regValue .r14 = _ at h
    rcases hm with rfl | rfl <;> exact h.trans (congrArg (fun p : BitVec 64 ↦ p + _) hs)

theorem full_prepare_advance [bindings : Bindings] {mode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true)
    (hs : stackPtr s = frameBase initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = startAddress mode .sha256 true true + (18 : BitVec 64) ∧
      t.regValue .r14 = frameBase initial .sha256 mode true true +
        BitVec.ofNat 64 (fullTempOffset mode) ∧
      t.regValue .rdi = t.regValue .r14 ∧
      t.regValue .rdx = 200 ∧ t.regValue .rsi = 0 ∧
      AgreesExcept [.reg 14, .reg 2, .reg 7, .reg 6, .flags, .rip] s t := by
  obtain ⟨a, ha, ia, pa, ra, aa⟩ := full_temp_advance hm hCall inv hp hs
  have spa : a.GPR[4] ≠ (returnBoundary initial).rsp := by
    have he : stackPtr a = stackPtr s := aa.read (r := 4) (n := 64) (by decide)
    change stackPtr a ≠ _
    rw [he, hs, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨b, hb, ib, spb, eb, ab⟩ := Reset.advanceNoMemory hCall
    (mov_r32_imm32_effect_step (startAddress mode .sha256 true true + 8) 0xba (by decide) 200)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 2, .rip]) (by simp only [movR32Imm32Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ia spa pa
  have pb : b.RIP = startAddress mode .sha256 true true + (13 : BitVec 64) := by
    simpa only [movR32Imm32Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using eb.rip
  obtain ⟨c, hc, ic, spc, ec, ac⟩ := Reset.advanceNoMemory hCall
    (mov_r64_r64_effect_step (startAddress mode .sha256 true true + 13) 0x4c 0xf7
      (by unfold RexWPrefix; decide) (by decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 7, .rip]) (by simp only [movR64R64Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ib spb pb
  have pc : c.RIP = startAddress mode .sha256 true true + (16 : BitVec 64) := by
    simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using ec.rip
  obtain ⟨t, ht, it, _, et, agt⟩ := Reset.advanceNoMemory hCall
    (xor_r32_r32_effect_step (startAddress mode .sha256 true true + 16) 0xf6 (by decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 6, .flags, .rip]) (by simp only [xorR32R32Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ic spc pc
  have r14 : t.regValue .r14 = a.regValue .r14 :=
    (agt.read (r := 14) (n := 64) (by decide)).trans
      ((ac.read (r := 14) (n := 64) (by decide)).trans
        (ab.read (r := 14) (n := 64) (by decide)))
  refine ⟨t, ha.trans (hb.trans (hc.trans ht)), it, ?_, r14.trans ra, ?_, ?_, ?_, ?_⟩
  · simpa only [xorR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using et.rip
  · have h := ec.writes
    change c.regValue .rdi = b.regValue .r14 at h
    exact (agt.read (r := 7) (n := 64) (by decide)).trans
      (h.trans ((ab.read (r := 14) (n := 64) (by decide)).trans r14.symm))
  · exact (agt.read (r := 2) (n := 64) (by decide)).trans
      ((ac.read (r := 2) (n := 64) (by decide)).trans eb.writes)
  · have h := et.writes
    change t.regValue .rsi = ((Operand.reg 6 : Operand 32).read c ^^^
      (Operand.reg 6 : Operand 32).read c).setWidth 64 at h
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using h
  · exact (aa.trans (ab.trans (ac.trans agt))).mono (by simp)

theorem full_memset_pre [bindings : Bindings] {mode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (ip : s.RIP = 0x106a20)
    (sp : stackPtr s = frameBase initial .sha256 mode true true - (8 : BitVec 64))
    (retLow : (stackTop s).toNat < 2^32)
    (destination : (Operand.reg 7 : Operand 64).read s =
      frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode))
    (length : (Operand.reg 2 : Operand 64).read s = 200)
    (value : (Operand.reg 6 : Operand 64).read s = 0) :
    Memset.Pre (returnBoundary initial) s 200 := by
  have budget : mode.frameSize .sha256 true true + 8 ≤
      (mode.entry .sha256 true true).minStackBytes := by rw [Mode.stackBudget mode .sha256 true true]; omega
  have bbase : mode.frameSize .sha256 true true ≤
      (mode.entry .sha256 true true).minStackBytes := by omega
  have temp : fullTempOffset mode + 200 ≤ mode.frameSize .sha256 true true := by
    rcases hm with rfl | rfl <;> decide +kernel
  have hptr := frameAddress_toNat hCall.stackAvailable bbase (by omega :
    fullTempOffset mode ≤ mode.frameSize .sha256 true true + 8)
  have hbase : (frameBase initial .sha256 mode true true).toNat =
      (initial.regValue .rsp).toNat - mode.frameSize .sha256 true true :=
    stack_sub_toNat hCall.stackAvailable.2.2.1 bbase
  have hsp : (stackPtr s).toNat = (initial.regValue .rsp).toNat -
      (mode.frameSize .sha256 true true + 8) := by
    rw [sp, frameBase_sub_eight (keccak := true) (fullState := true)]
    exact stack_sub_toNat hCall.stackAvailable.2.2.1 budget
  have hmin : (mode.entry .sha256 true true).minStackBytes ≤
      (initial.regValue .rsp).toNat := hCall.stackAvailable.2.2.1
  obtain ⟨hlo, hhi⟩ := frameBase_bounds hCall.stackAvailable bbase
  have low : (Stack.region initial (mode.entry .sha256 true true).minStackBytes).start +
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).size < 2^32 :=
    hCall.stackAvailable.1
  refine ⟨ip, length, value, ?_, inv.direction, ?_, ?_, ?_, ?_, retLow, ?_, ?_, ?_⟩
  · rw [destination, hptr, hbase]
    have halign : (initial.regValue .rsp).toNat % 16 = 8 := hCall.stackAvailable.2.2.2
    rcases hm with rfl | rfl <;> simp only [Mode.frameSize, fullTempOffset, reduceCtorEq, ↓reduceIte] at * <;> omega
  · rw [destination]
    exact inv.frameReadable hCall.stackAvailable (by omega)
  · rw [destination]
    intro a ha ht
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial .sha256 mode true true)
      a (digest_region_contains hCall.stackAvailable
        (by rcases hm with rfl | rfl <;> decide +kernel) ha) (.inr ht)
  · rw [destination]
    intro a ha ht
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial .sha256 mode true true)
      a (digest_region_contains hCall.stackAvailable
        (by rcases hm with rfl | rfl <;> decide +kernel) ha) (.inl ht)
  · apply memReadable_of_region hCall.stackAvailable.1 (inv.stackAllocated hCall.stackAvailable)
    · simp only [hsp, Stack.region]
      omega
    · simp only [hsp, Stack.region, Stack.returnAddressBytes]
      omega
  · rw [destination]
    apply RangeApart.of_toNat
    · rw [hptr]; omega
    · rw [hsp]; omega
    · rw [hptr, hsp, hbase]
      exact .inr (by omega)
  · rw [sp, frameBase_sub_eight (keccak := true) (fullState := true)]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  · right
    rw [sp, BitVec.sub_add_cancel, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel

theorem full_memset_call [bindings : Bindings] {mode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true + (18 : BitVec 64))
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hDigestMemset : mode = .digest → s.regValue .r13 = 0x106a20) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = 0x106a20 ∧
      stackPtr t = frameBase initial .sha256 mode true true - (8 : BitVec 64) ∧
      stackTop t = startAddress mode .sha256 true true +
        (if mode = .digest then 21 else 24 : BitVec 64) ∧
      AgreesExcept [.reg 4, .mem (frameBase initial .sha256 mode true true - (8 : BitVec 64)) 8, .rip] s t := by
  obtain ⟨t, ht, it, pt, st, rt, ag⟩ := initial_memset_call_form
    (returnBoundary initial) (startAddress mode .sha256 true true + 18) 0x0fdda1
    (decide (mode = .digest)) hCall
    (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (by rcases hm with rfl | rfl
        · change (startAddress .plain .sha256 true true + 18 + 6 : BitVec 64) +
            (0x0fdda1 : BitVec 32).signExtend 64 = 0x200188
          decide +kernel
        · exact hDigestMemset rfl)
    inv hp hs (by
      rw [frameBase_sub_eight (keccak := true) (fullState := true)]
      apply stackSub_ne_returnBoundary
      rcases hm with rfl | rfl <;> decide +kernel)
  refine ⟨t, ht, it, pt, st, ?_, ag⟩
  rcases hm with rfl | rfl <;> exact rt

theorem full_called_memset [bindings : Bindings] (hstride : UnitStringStride bindings)
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (ip : s.RIP = 0x106a20)
    (sp : stackPtr s = frameBase initial .sha256 mode true true - (8 : BitVec 64))
    (retLow : (stackTop s).toNat < 2^32)
    (destination : (Operand.reg 7 : Operand 64).read s =
      frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode))
    (length : (Operand.reg 2 : Operand 64).read s = 200)
    (value : (Operand.reg 6 : Operand 64).read s = 0) :
    ∃ t, Advances (returnBoundary initial) 45 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = stackTop s ∧ stackPtr t = frameBase initial .sha256 mode true true ∧
      AgreesExcept (Memset.clobbers
        (frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode)) 200) s t := by
  obtain ⟨t, ht, done⟩ := Memset.memset200_steps hstride (returnBoundary initial) s
    inv.ready inv.code (full_memset_pre hm hCall inv ip sp retLow destination length value)
  have frame : AgreesExcept (Memset.clobbers
      (frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode)) 200) s t :=
    destination ▸ done.agrees
  refine ⟨t, ht, inv.of_agreesExcept hCall done.ready frame ?_ (by simp [Memset.clobbers]), done.rip, ?_, frame⟩
  · apply Memset.clobbers_writesWithin
    intro i hi
    refine ⟨_, stack_mem_writeRegions initial .sha256 mode true true, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply frameAddress_contains hCall.stackAvailable
      (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    have htemp : fullTempOffset mode + 200 ≤ mode.frameSize .sha256 true true := by
      rcases hm with rfl | rfl <;> decide +kernel
    omega
  · rw [done.rsp, sp, BitVec.sub_add_cancel]

def fullZeroChanges (initial : RamState) (mode : Mode) : List Component :=
  [.reg 14, .reg 2, .reg 7, .reg 6, .flags, .rip] ++
    [.reg 4, .mem (frameBase initial .sha256 mode true true - (8 : BitVec 64)) 8, .rip] ++
    Memset.clobbers (frameBase initial .sha256 mode true true +
      BitVec.ofNat 64 (fullTempOffset mode)) 200

theorem full_zero_advance [bindings : Bindings] (hstride : UnitStringStride bindings)
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hDigestMemset : mode = .digest → s.regValue .r13 = 0x106a20) :
    ∃ t, Advances (returnBoundary initial) 50 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = startAddress mode .sha256 true true +
        (if mode = .digest then 21 else 24 : BitVec 64) ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      t.regValue .r14 = frameBase initial .sha256 mode true true +
        BitVec.ofNat 64 (fullTempOffset mode) ∧
      AgreesExcept (fullZeroChanges initial mode) s t := by
  obtain ⟨a, ha, ia, pa, ra, da, la, va, aa⟩ := full_prepare_advance hm hCall inv hp hs
  have spa : stackPtr a = frameBase initial .sha256 mode true true :=
    (aa.read (r := 4) (n := 64) (by decide)).trans hs
  obtain ⟨b, hb, ib, pb, spb, rb, ab⟩ := full_memset_call hm hCall ia pa spa (by
    intro hd
    exact (aa.read (r := 13) (n := 64) (by decide)).trans (hDigestMemset hd))
  have db : (Operand.reg 7 : Operand 64).read b =
      frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode) :=
    (ab.read (r := 7) (n := 64) (by simp)).trans (da.trans ra)
  obtain ⟨t, ht, it, pt, st, ag⟩ := full_called_memset hstride hm hCall ib pb spb
    (by rw [rb]; rcases hm with rfl | rfl <;> decide +kernel) db
    ((ab.read (r := 2) (n := 64) (by simp)).trans la)
    ((ab.read (r := 6) (n := 64) (by simp)).trans va)
  refine ⟨t, ha.trans (hb.trans ht), it, pt.trans rb, st, ?_, ?_⟩
  · exact (ag.read (r := 14) (n := 64) (by simp [Memset.clobbers])).trans
      ((ab.read (r := 14) (n := 64) (by simp)).trans ra)
  · simpa only [fullZeroChanges, List.append_assoc] using aa.trans (ab.trans ag)

theorem full_state_advance [bindings : Bindings]
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true +
      (if mode = .digest then 21 else 24 : BitVec 64))
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hDigestState : mode = .digest → s.regValue .r12 = statePointer initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = callAddress mode .sha256 true true - (3 : BitVec 64) ∧
      t.regValue .rdi = statePointer initial .sha256 mode true true ∧
      AgreesExcept [.reg 7, .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  rcases hm with rfl | rfl
  · obtain ⟨t, ht, it, _, et, ag⟩ := Reset.advanceNoMemory hCall
      (lea_r64_effect_step (startAddress .plain .sha256 true true + 24) 0x48
        (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 8))
        (by decide) (by decide) (by decide))
      (by unfold ImageAt; decide +kernel)
      (changes := [.reg 7, .rip]) (by simp only [leaR64Effect_components]; decide)
      (by simp [Component.Covers]) (by decide) inv hsp hp
    refine ⟨t, ht, it, et.rip, ?_, ag⟩
    have h := et.writes
    change t.regValue .rdi = stackPtr s + 8 at h
    exact h.trans (congrArg (fun p : BitVec 64 ↦ p + 8) hs)
  · obtain ⟨t, ht, it, _, et, ag⟩ := Reset.advanceNoMemory hCall
      (mov_r64_r64_effect_step (startAddress .digest .sha256 true true + 21) 0x4c 0xe7
        (by unfold RexWPrefix; decide) (by decide))
      (by unfold ImageAt; decide +kernel)
      (changes := [.reg 7, .rip]) (by simp only [movR64R64Effect_components]; decide)
      (by simp [Component.Covers]) (by decide) inv hsp hp
    refine ⟨t, ht, it, et.rip, ?_, ag⟩
    exact et.writes.trans (hDigestState rfl)

theorem full_arguments_advance [bindings : Bindings]
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true +
      (if mode = .digest then 21 else 24 : BitVec 64))
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hTemp : s.regValue .r14 = frameBase initial .sha256 mode true true +
      BitVec.ofNat 64 (fullTempOffset mode))
    (hDigestState : mode = .digest → s.regValue .r12 = statePointer initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = callAddress mode .sha256 true true ∧
      t.regValue .rdi = statePointer initial .sha256 mode true true ∧
      t.regValue .rsi = frameBase initial .sha256 mode true true +
        BitVec.ofNat 64 (fullTempOffset mode) ∧
      AgreesExcept [.reg 7, .reg 6, .rip] s t := by
  obtain ⟨a, ha, ia, pa, da, aa⟩ := full_state_advance hm hCall inv hp hs hDigestState
  have hsp : a.GPR[4] ≠ (returnBoundary initial).rsp := by
    have sp : stackPtr a = frameBase initial .sha256 mode true true :=
      (aa.read (r := 4) (n := 64) (by decide)).trans hs
    change stackPtr a ≠ _
    rw [sp, frameBase]
    apply stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨t, ht, it, _, et, ag⟩ := Reset.advanceNoMemory hCall
    (mov_r64_r64_effect_step (callAddress mode .sha256 true true - 3) 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := [.reg 6, .rip]) (by simp only [movR64R64Effect_components]; decide)
    (by simp [Component.Covers]) (by decide) ia hsp pa
  refine ⟨t, ha.trans ht, it, ?_, ?_, ?_, (aa.trans ag).mono (by simp)⟩
  · simpa only [movR64R64Effect, BitVec.sub_add_cancel] using et.rip
  · exact (ag.read (r := 7) (n := 64) (by decide)).trans da
  · exact et.writes.trans ((aa.read (r := 14) (n := 64) (by decide)).trans hTemp)

theorem full_finalize_pre [bindings : Bindings]
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    {state : Incremental.State}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = Finalize.entryAddress .sha256 false true true)
    (hs : s.regValue .rsp = frameBase initial .sha256 mode true true - 8)
    (hd : s.regValue .rdi = statePointer initial .sha256 mode true true)
    (ho : s.regValue .rsi = frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode))
    (hc : state.cursor < Variant.sha256.rate)
    (hmdata : (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hlanes : Permutation.memoryLanes (statePointer initial .sha256 mode true true) s = state.lanes)
    (hr : stackTop s = callAddress mode .sha256 true true + 5) :
    Finalize.CallPre (returnBoundary initial) .sha256 false state s true true := by
  have bounds : mode.stateOffset .sha256 true true + 201 ≤
      mode.frameSize .sha256 true true - 8 * mode.pushCount true := by
    rcases hm with rfl | rfl <;> decide +kernel
  apply finalizeCallPre hCall inv bounds
    (by rcases hm with rfl | rfl <;> decide +kernel) hp hs hd ho
    (digest_output_valid hCall.stackAvailable (by rcases hm with rfl | rfl <;> decide +kernel)) ?_ ?_ ?_ hc hmdata hlanes ?_
  · intro i hi
    refine ⟨_, stack_mem_writeRegions initial .sha256 mode true true, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply frameAddress_contains hCall.stackAvailable
      (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    have ht : fullTempOffset mode + 200 ≤ mode.frameSize .sha256 true true := by
      rcases hm with rfl | rfl <;> decide +kernel
    change i < 200 at hi
    omega
  · have hf : Finalize.frameBase s = frameBase initial .sha256 mode true true - 304 := by
      simp only [Finalize.frameBase, hs, BitVec.sub_sub]; rfl
    rw [hf]
    have he : frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode) =
        (frameBase initial .sha256 mode true true - 304) + BitVec.ofNat 64 (304 + fullTempOffset mode) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [he]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Variant.digestBytes, ↓reduceIte] using
      (RangeApart.offsets (frameBase initial .sha256 mode true true - 304)
        (a := 304 + fullTempOffset mode) (b := 0) (len := 200) (count := 304)
        (by rcases hm with rfl | rfl <;> decide +kernel) (by decide) (.inr (by omega)))
  · exact RangeApart.offsets (frameBase initial .sha256 mode true true)
      (a := fullTempOffset mode) (b := mode.stateOffset .sha256 true true) (len := 200) (count := 201)
      (by rcases hm with rfl | rfl <;> decide +kernel)
      (by rcases hm with rfl | rfl <;> decide +kernel)
      (.inr (by rcases hm with rfl | rfl <;> decide +kernel))
  · rw [hr]
    refine ⟨0x4c, ?_⟩
    apply imageSections_mem_toCodeMap_of_fetchByte
    rcases hm with rfl | rfl <;> decide +kernel

theorem full_called_finalize [bindings : Bindings] (hstride : UnitStringStride bindings)
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    {state : Incremental.State}
    (hm : mode = .plain ∨ mode = .digest) (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = Finalize.entryAddress .sha256 false true true)
    (hs : s.regValue .rsp = frameBase initial .sha256 mode true true - 8)
    (hd : s.regValue .rdi = statePointer initial .sha256 mode true true)
    (ho : s.regValue .rsi = frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode))
    (hc : state.cursor < Variant.sha256.rate)
    (hmdata : (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hlanes : Permutation.memoryLanes (statePointer initial .sha256 mode true true) s = state.lanes)
    (hr : stackTop s = callAddress mode .sha256 true true + 5) :
    ∃ t, Advances (returnBoundary initial) (6359 + Memcpy.memcpy200Steps (s.regValue .rsi)) s t ∧
      Invariant initial .sha256 mode t true true ∧
      Finalize.CallResult .sha256 false state s t true true ∧
      MemoryWriteFrame s t #v[Stack.region initial (mode.entry .sha256 true true).minStackBytes] := by
  obtain ⟨t, ht, ready, _, result⟩ := Finalize.full_call_advance hstride false state
    (returnBoundary initial) (validInvocation_returnBoundary_bounds hInitial hCall).2
    s inv.ready inv.code (full_finalize_pre hm hCall inv hp hs hd ho hc hmdata hlanes hr) (by
      change s.regValue .rsp - 0#64 ≠ (returnBoundary initial).rsp
      rw [BitVec.sub_zero, hs, frameBase_sub_eight (keccak := true) (fullState := true)]
      apply stackSub_ne_returnBoundary
      rcases hm with rfl | rfl <;> decide +kernel)
  have bounds : mode.stateOffset .sha256 true true + 201 ≤
      mode.frameSize .sha256 true true - 8 * mode.pushCount true := by
    rcases hm with rfl | rfl <;> decide +kernel
  have memory : MemoryWriteFrame s t
      #v[Stack.region initial (mode.entry .sha256 true true).minStackBytes] := by
    apply memoryWriteFrame_mono result.memory
    intro region hregion address ha
    obtain ⟨r, hr, hc⟩ := finalizeWrites_cover hCall.stackAvailable bounds hs hd ho
      (regions := #v[Stack.region initial (mode.entry .sha256 true true).minStackBytes,
        ⟨(frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode)).toNat, 200⟩])
      (Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩)
      (Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩) region hregion address ha
    refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp hr
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact hc
    · exact digest_region_contains hCall.stackAvailable
        (by rcases hm with rfl | rfl <;> decide +kernel) hc
  refine ⟨t, ht, inv.of_callResult hCall ready memory ?_ result.grows result.rest, result, memory⟩
  intro region hregion address ha
  have he : region = Stack.region initial (mode.entry .sha256 true true).minStackBytes := by
    simpa using hregion
  exact ⟨_, stack_mem_writeRegions initial .sha256 mode true true, he ▸ ha⟩

theorem fullZeroChanges_cover {initial : RamState} {mode : Mode} {c : Component}
    (hc : c ∈ fullZeroChanges initial mode) {a : BitVec 64} (ha : c.Covers a) :
    (Component.mem (frameBase initial .sha256 mode true true - (8 : BitVec 64)) 8).Covers a ∨
    (Component.mem (frameBase initial .sha256 mode true true +
      BitVec.ofNat 64 (fullTempOffset mode)) 200).Covers a := by
  simp only [fullZeroChanges, Memset.clobbers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first | exact ha.elim | exact .inl ha | exact .inr ha

theorem fullZeroChanges_read {initial s t : RamState} {mode : Mode} {offset width : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (ha : AgreesExcept (fullZeroChanges initial mode) s t)
    (hbound : offset + width / 8 ≤ fullTempOffset mode) :
    (Operand.mem (frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [ha.byte (by
    intro c hc hcover
    rcases fullZeroChanges_cover hc hcover with hslot | htemp
    · obtain ⟨i, hi, he⟩ := hslot
      have apart := RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
        (a := 0) (b := 8 + offset) (len := 8) (count := width / 8)
        (by decide) (by rcases hm with rfl | rfl <;> simp only [fullTempOffset, reduceCtorEq, ↓reduceIte] at hbound <;> omega)
        (.inl (by omega))
      apply apart i hi j hj
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        ← BitVec.add_assoc, BitVec.sub_add_cancel] using he.symm
    · obtain ⟨i, hi, he⟩ := htemp
      have apart := RangeApart.offsets (frameBase initial .sha256 mode true true)
        (a := fullTempOffset mode) (b := offset) (len := 200) (count := width / 8)
        (by rcases hm with rfl | rfl <;> decide +kernel)
        (by rcases hm with rfl | rfl <;> simp only [fullTempOffset, reduceCtorEq, ↓reduceIte] at hbound <;> omega)
        (.inr hbound)
      exact apart i hi j hj he.symm)]

theorem fullZeroChanges_saved {initial s t : RamState} {mode : Mode}
    (hm : mode = .plain ∨ mode = .digest)
    (hs : SavedFrame initial s mode true)
    (ha : AgreesExcept (fullZeroChanges initial mode) s t) : SavedFrame initial t mode true := by
  apply hs.of_localFrame (v := .sha256) (keccak := true) ha
  intro c hc a hcover
  rcases fullZeroChanges_cover hc hcover with hslot | htemp
  · obtain ⟨i, hi, rfl⟩ := hslot
    refine ⟨i, ?_, rfl⟩
    rcases hm with rfl | rfl <;> simp only [Mode.frameSize, Mode.pushCount, ↓reduceIte] <;> omega
  · obtain ⟨i, hi, rfl⟩ := htemp
    refine ⟨8 + fullTempOffset mode + i, ?_, ?_⟩
    · rcases hm with rfl | rfl <;>
        simp only [Mode.frameSize, Mode.pushCount, fullTempOffset, reduceCtorEq, ↓reduceIte] <;> omega
    · rw [BitVec.ofNat_add, BitVec.ofNat_add, ← BitVec.add_assoc,
        ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel]

theorem full_to_call [bindings : Bindings] (hstride : UnitStringStride bindings)
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = startAddress mode .sha256 true true)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hDigestState : mode = .digest → s.regValue .r12 = statePointer initial .sha256 mode true true)
    (hDigestMemset : mode = .digest → s.regValue .r13 = 0x106a20) :
    ∃ t, Advances (returnBoundary initial) 53 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = Finalize.entryAddress .sha256 false true true ∧
      stackPtr t = frameBase initial .sha256 mode true true - (8 : BitVec 64) ∧
      t.regValue .rdi = statePointer initial .sha256 mode true true ∧
      t.regValue .rsi = frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode) ∧
      t.regValue .r14 = frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode) ∧
      stackTop t = callAddress mode .sha256 true true + 5 ∧
      AgreesExcept (fullZeroChanges initial mode) s t := by
  obtain ⟨a, ha, ia, pa, sa, ta, aa⟩ := full_zero_advance hstride hm hCall inv hp hs hDigestMemset
  obtain ⟨b, hb, ib, pb, db, ob, ab⟩ := full_arguments_advance hm hCall ia pa sa ta (by
    intro hd
    exact (aa.read (r := 12) (n := 64) (by simp [fullZeroChanges, Memset.clobbers])).trans (hDigestState hd))
  have sb : stackPtr b = frameBase initial .sha256 mode true true :=
    (ab.read (r := 4) (n := 64) (by decide)).trans sa
  obtain ⟨t, ht, it, pt, st, rt, ag, _⟩ := directCallAt
    (mode.frameSize .sha256 true true) (callAddress mode .sha256 true true)
    (callDisplacement mode .sha256 true true) hCall
    (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    (by rcases hm with rfl | rfl <;> decide +kernel) ib pb sb
    (callCode_subset mode .sha256 true true)
    (by rw [call_target mode .sha256 true true]; decide +kernel)
  have ag' : AgreesExcept [.reg 4,
      .mem (frameBase initial .sha256 mode true true - (8 : BitVec 64)) 8, .rip] b t := by
    simpa only [frameBase_sub_eight (keccak := true) (fullState := true)] using ag
  have ab' : AgreesExcept (fullZeroChanges initial mode) a b := ab.mono (by
    simp [fullZeroChanges, Memset.clobbers])
  have ag'' : AgreesExcept (fullZeroChanges initial mode) b t := ag'.mono (by
    simp [fullZeroChanges, Memset.clobbers])
  refine ⟨t, ha.trans (hb.trans ht), it, ?_, ?_, ?_, ?_, ?_, rt, ?_⟩
  · rw [call_target mode .sha256 true true] at pt
    exact pt
  · simpa only [frameBase_sub_eight (keccak := true) (fullState := true)] using st
  · exact (ag'.read (r := 7) (n := 64) (by simp)).trans db
  · exact (ag'.read (r := 6) (n := 64) (by simp)).trans ob
  · exact (ag'.read (r := 14) (n := 64) (by simp)).trans
      ((ab.read (r := 14) (n := 64) (by decide)).trans ta)
  · exact (aa.trans (ab'.trans ag'')).mono (by simp)

theorem fullZeroChanges_writes {initial : RamState} {mode : Mode}
    (hm : mode = .plain ∨ mode = .digest)
    (hs : Stack.Valid initial (mode.entry .sha256 true true).minStackBytes) :
    WritesWithin (fullZeroChanges initial mode)
      #v[Stack.region initial (mode.entry .sha256 true true).minStackBytes] := by
  intro c hc a hcover
  refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
  rcases fullZeroChanges_cover hc hcover with hslot | htemp
  · obtain ⟨i, hi, rfl⟩ := hslot
    rw [frameBase_sub_eight (keccak := true) (fullState := true)]
    apply stack_sub_contains hs
      (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    omega
  · obtain ⟨i, hi, rfl⟩ := htemp
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply frameAddress_contains hs
      (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    have htemp : fullTempOffset mode + 200 ≤ mode.frameSize .sha256 true true := by
      rcases hm with rfl | rfl <;> decide +kernel
    omega

theorem fullZeroChanges_output {initial s t : RamState} {mode : Mode}
    (hm : mode = .plain ∨ mode = .digest)
    (ha : AgreesExcept (fullZeroChanges initial mode) s t) :
    (outputOperand initial .sha256 mode true true).read t =
      (outputOperand initial .sha256 mode true true).read s := by
  rcases hm with rfl | rfl
  · have h := fullZeroChanges_read (Or.inl rfl) ha (offset := 0) (width := 64) (by decide)
    simpa only [outputOperand, outputSlot, Mode.outputSlotOffset, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using h
  · exact ha.read (r := 3) (n := 64) (by simp [fullZeroChanges, Memset.clobbers])

theorem full_finish_advance [bindings : Bindings] (hstride : UnitStringStride bindings)
    {mode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    {state : Incremental.State} {out : BitVec 64}
    (hm : mode = .plain ∨ mode = .digest) (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true) (saved : SavedFrame initial s mode true)
    (hp : s.RIP = startAddress mode .sha256 true true)
    (hs : stackPtr s = frameBase initial .sha256 mode true true)
    (hOutput : (outputOperand initial .sha256 mode true true).read s = out)
    (hc : state.cursor < Variant.sha256.rate)
    (hmdata : (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hlanes : Permutation.memoryLanes (statePointer initial .sha256 mode true true) s = state.lanes)
    (hDigestState : mode = .digest → s.regValue .r12 = statePointer initial .sha256 mode true true)
    (hDigestMemset : mode = .digest → s.regValue .r13 = 0x106a20) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial .sha256 mode t true true ∧ SavedFrame initial t mode true ∧
      t.RIP = callAddress mode .sha256 true true + (5 : BitVec 64) ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      t.regValue .r14 = frameBase initial .sha256 mode true true + BitVec.ofNat 64 (fullTempOffset mode) ∧
      (outputOperand initial .sha256 mode true true).read t = out ∧
      (∀ i : Fin 200, t.external[frameBase initial .sha256 mode true true +
          BitVec.ofNat 64 (fullTempOffset mode) + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest .sha256 state true true)[i]) ∧
      t.regValue .rbp = s.regValue .rbp ∧
      MemoryWriteFrame s t #v[Stack.region initial (mode.entry .sha256 true true).minStackBytes] := by
  obtain ⟨a, ha, ia, pa, sa, da, oa, ta, ra, ag⟩ :=
    full_to_call hstride hm hCall inv hp hs hDigestState hDigestMemset
  change a.regValue .rsp = frameBase initial .sha256 mode true true - (8 : BitVec 64) at sa
  have ma : (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read a =
      BitVec.ofNat 8 state.cursor := by
    have h := fullZeroChanges_read hm ag
      (offset := mode.stateOffset .sha256 true true + 200) (width := 8)
      (by rcases hm with rfl | rfl <;> decide +kernel)
    have h' : (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read a =
        (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read s := by
      simpa only [statePointer, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
    exact h'.trans hmdata
  have la : Permutation.memoryLanes (statePointer initial .sha256 mode true true) a = state.lanes := by
    rw [← hlanes]
    funext lane
    have hn := lane.isLt
    have h := fullZeroChanges_read hm ag
      (offset := mode.stateOffset .sha256 true true + 8 * lane.val) (width := 64)
      (by rcases hm with rfl | rfl <;>
        simp only [Mode.stateOffset, fullTempOffset, reduceCtorEq, ↓reduceIte] <;> omega)
    simpa only [Permutation.memoryLanes, statePointer, BitVec.ofNat_add, ← BitVec.add_assoc] using h
  obtain ⟨t, ht, it, result, memory⟩ := full_called_finalize hstride hm hInitial hCall ia pa sa da oa hc ma la ra
  have bounds : mode.stateOffset .sha256 true true + 201 ≤
      mode.frameSize .sha256 true true - 8 * mode.pushCount true := by
    rcases hm with rfl | rfl <;> decide +kernel
  have sv := finalizeMemory_saved hCall.stackAvailable bounds sa da oa
    (Or.inr (digest_below_saved hCall.stackAvailable (by rcases hm with rfl | rfl <;> decide +kernel)))
    result.memory (fullZeroChanges_saved hm saved ag)
  refine ⟨_, t, ha.trans ht, it, sv, result.rip.trans ra, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.regValue .rsp = _
    rw [result.stack, sa, BitVec.sub_add_cancel]
  · exact (result.saved .r14 (by simp)).trans ta
  · exact (finalize_slot_read hm hCall.stackAvailable sa da oa result.memory result.saved
      (by rcases hm with rfl | rfl <;> decide +kernel)
      (by intro he; subst mode; left; decide +kernel)).trans
        ((fullZeroChanges_output hm ag).trans hOutput)
  · intro i
    rw [← oa]
    exact result.output i
  · exact (result.saved .rbp (by simp)).trans
      (ag.read (r := 5) (n := 64) (by simp [fullZeroChanges, Memset.clobbers]))
  · exact memoryWriteFrame_trans (ag.memoryWriteFrame (fullZeroChanges_writes hm hCall.stackAvailable)) memory

end Sha3.Proofs.Wrapper.Finish.Plain

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem finish_plain_full [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {mode : Mode} {inputs : Array Input} {split : Nat}
    {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (hInv : Invariant initial .sha256 mode s true true) (hSaved : SavedFrame initial s mode true)
    (hRip : s.RIP = startAddress mode .sha256 true true)
    (hRsp : stackPtr s = frameBase initial .sha256 mode true true)
    (hOutput : (outputOperand initial .sha256 mode true true).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, 200⟩)
    (hMember : (⟨out.toNat, 200⟩ : MemoryRegion) ∈ writeRegions initial .sha256 mode true true)
    (hApart : (⟨out.toNat, 200⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes))
    (hCursor : state.cursor < Variant.sha256.rate)
    (hMetadata : (Operand.mem (statePointer initial .sha256 mode true true + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial .sha256 mode true true) s = state.lanes)
    (hMode : mode = .plain ∨ mode = .digest)
    (hPreserved : ∀ j : Fin 6,
      (∀ i : Fin (mode.pushCount true),
        (epiloguePopReg mode true i).setWidth 5 ≠ (epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
        initial.regValue savedRegisters[j])
    (hDigestState : mode = .digest → s.regValue .r12 = statePointer initial .sha256 mode true true)
    (hDigestMemset : mode = .digest → s.regValue .r13 = 0x106a20) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      Invariant initial .sha256 mode final true true ∧
      (∀ i : Fin 200, final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest .sha256 state true true)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (finalWrites initial .sha256 mode out true true) := by
  obtain ⟨n, a, ha, ia, sva, pa, sa, ta, oa, ba, rbpa, ma⟩ :=
    Plain.full_finish_advance hStride hMode hInitial hCall hInv hSaved hRip hRsp hOutput
      hCursor hMetadata hLanes hDigestState hDigestMemset
  obtain ⟨m, b, hb, ib, svb, pb, sb, bb, mb, rbpb⟩ :=
    Plain.full_copy_advance hStride hMode hCall ia sva pa sa ta oa hOut hMember hApart ba
  have preserved : ∀ j : Fin 6,
      (∀ i : Fin (mode.pushCount true),
        (epiloguePopReg mode true i).setWidth 5 ≠ (epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read b =
        initial.regValue savedRegisters[j] := by
    intro j hj
    have hp := hPreserved j hj
    rcases hMode with rfl | rfl
    · exact False.elim (hj j rfl)
    · have only : ∀ j : Fin 6,
          (∀ i : Fin (Mode.digest.pushCount true),
            (epiloguePopReg .digest true i).setWidth 5 ≠
              (epiloguePopReg .plain false j).setWidth 5) → j = 5 := by decide +kernel
      have he := only j hj
      subst j
      exact (rbpb.trans rbpa).trans hp
  obtain ⟨final, hf, invf, memf, savedf⟩ :=
    returnFromEpilogue hInitial hCall ib svb pb sb preserved
  refine ⟨_, final, ha.returns (hb.returns hf), invf, ?_, savedf, ?_⟩
  · intro i
    rw [memf]
    exact bb i
  · have cover : ∀ r ∈ #v[Stack.region initial (mode.entry .sha256 true true).minStackBytes],
        ∀ a, r.Contains a → ∃ t ∈ finalWrites initial .sha256 mode out true true, t.Contains a := by
      intro r hr a ha
      have he : r = Stack.region initial (mode.entry .sha256 true true).minStackBytes := by simpa using hr
      exact ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, he ▸ ha⟩
    have mem := memoryWriteFrame_trans (memoryWriteFrame_mono ma cover) mb
    intro a ha
    rw [memf]
    exact mem a ha

end Sha3.Proofs.Wrapper.Finish
