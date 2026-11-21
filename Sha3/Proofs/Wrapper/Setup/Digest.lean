import Sha3.Proofs.Wrapper.Setup.Prefix

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def digestSetupTail (v : Variant) (fullState : Bool) : Nat :=
  match fullState, v with
  | true, _ => 19
  | false, .sha512 => 17
  | false, _ => 14

def digestSetupBytes (v : Variant) (fullState : Bool) : List UInt8 :=
  [0x48, 0x89, 0xd3, 0x49, 0x89, 0xf6, 0x49, 0x89, 0xff] ++
  (if fullState then [0x49, 0x89, 0xe4, 0x4c, 0x8d, 0x2d, 0xcd, 0x49, 0, 0]
   else encodeLeaR64M 12 (plainStateAddr v)) ++
  [0xba, 0xc9, 0, 0, 0, 0x4c, 0x89, 0xe7, 0x31, 0xf6]

theorem digest_setup_steps [bindings : Bindings] {initial s : RamState} {v : Variant}
    {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (p : BitVec 64)
    (hCall : ValidInvocation bindings v .digest initial inputs split keccak fullState)
    (image : ImageAt p (digestSetupBytes v fullState))
    (inv : Invariant initial v .digest s keccak fullState)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial v .digest keccak fullState)
    (inside : s.GPR[4] ≠ boundary.rsp)
    (args : ∀ r ∈ [Syntax.Reg.rdx, .rsi, .rdi, .rbp, .r13],
      s.regValue r = initial.regValue r) :
    ∃ t, Advances boundary (if fullState then 8 else 7) s t ∧
      Invariant initial v .digest t keccak fullState ∧
      t.RIP = p + BitVec.ofNat 64 (digestSetupTail v fullState + 10) ∧
      SetupRegisters initial v .digest t keccak fullState ∧
      SetupArguments initial v .digest t keccak fullState ∧
      (fullState = true → (Operand.reg 13 : Operand 64).read t = p + 0x49e0) ∧
      AgreesExcept (setupChanges initial v .digest keccak fullState) s t := by
  obtain ⟨s1, h1, i1, sp1, e1, o1, a1⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (0)) 3 2) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (0)) 0x48 0xd3 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (0) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    inv inside (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ip) (Obs.refl s)
  obtain ⟨s2, h2, i2, sp2, e2, o2, a2⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (3)) 14 6) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (3)) 0x49 0xf6 (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (3) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i1 sp1 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e1.rip) o1
  obtain ⟨s3, h3, i3, sp3, e3, o3, a3⟩ := setupAdvance
    (effect := movR64R64Effect (p + BitVec.ofNat 64 (6)) 15 7) hCall
    (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (6)) 0x49 0xff (by unfold RexWPrefix; decide) (by decide))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (6) (by cases fullState <;> cases v <;> decide +kernel))
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by
      intro c hc
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [setupChanges])
    i2 sp2 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e2.rip) o2
  cases fullState
  ·
    obtain ⟨s4, h4, i4, sp4, e4, o4, a4⟩ := setupAdvance
      (effect := leaR64Effect (p + BitVec.ofNat 64 (9)) 12 (plainStateAddr v)) hCall
      (lea_r64_effect_step (p + BitVec.ofNat 64 (9)) 0x4c (by unfold RexWPrefix; decide) 4 (plainStateAddr v) (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (9) (by cases v <;> decide +kernel))
      (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
      (by
        intro c hc
        simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i3 sp3 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e3.rip) o3
    obtain ⟨s5, h5, i5, sp5, e5, o5, a5⟩ := setupAdvance
      (effect := movR32Imm32Effect (p + BitVec.ofNat 64 (digestSetupTail v false)) 5 2 201) hCall
      (mov_r32_imm32_effect_step (p + BitVec.ofNat 64 (digestSetupTail v false)) 0xba (by decide) 201)
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (digestSetupTail v false) (by cases v <;> decide +kernel))
      (by intro t; simp [movR32Imm32Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [movR32Imm32Effect])
      (by
        intro c hc
        simp only [movR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i4 sp4 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e4.rip) o4
    obtain ⟨s6, h6, i6, sp6, e6, o6, a6⟩ := setupAdvance
      (effect := movR64R64Effect (p + BitVec.ofNat 64 (digestSetupTail v false + 5)) 7 12) hCall
      (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (digestSetupTail v false + 5)) 0x4c 0xe7 (by unfold RexWPrefix; decide) (by decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (digestSetupTail v false + 5) (by cases v <;> decide +kernel))
      (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [movR64R64Effect, h.read_reg])
      (by
        intro c hc
        simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i5 sp5 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e5.rip) o5
    obtain ⟨s7, h7, i7, sp7, e7, o7, a7⟩ := setupAdvance
      (effect := xorR32R32Effect (p + BitVec.ofNat 64 (digestSetupTail v false + 8)) 2 6 6) hCall
      (xor_r32_r32_effect_step (p + BitVec.ofNat 64 (digestSetupTail v false + 8)) 0xf6 (by decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (digestSetupTail v false + 8) (by cases v <;> decide +kernel))
      (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
      (by
        intro c hc
        simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [setupChanges])
      i6 sp6 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e6.rip) o6
    have hs := (o7.read (Operand.reg 4 : Operand 64) trivial).symm
    have hd := (o7.read (Operand.reg 7 : Operand 64) trivial).symm
    have hl := (o7.read (Operand.reg 2 : Operand 64) trivial).symm
    have hv := (o7.read (Operand.reg 6 : Operand 64) trivial).symm
    have hp := (o7.read (Operand.reg 15 : Operand 64) trivial).symm
    have hn := (o7.read (Operand.reg 14 : Operand 64) trivial).symm
    have hb := (o7.read (Operand.reg 3 : Operand 64) trivial).symm
    have hr := (o7.read (Operand.reg 12 : Operand 64) trivial).symm
    have hz := (o7.read (Operand.reg 5 : Operand 64) trivial).symm
    have ht := (o7.read (Operand.reg 13 : Operand 64) trivial).symm
    x86_norm [movR64R64Effect, leaR64Effect, movR32Imm32Effect,
      xorR32R32Effect, BitVec.xor_self, plainStateAddr] at hs hd hl hv hp hn hb hr hz ht
    change (Operand.reg 4 : Operand 64).read s = frameBase initial v .digest keccak false at sp
    simp only [BitVec.ofNat_eq_ofNat] at sp
    rw [sp] at hs hd hr
    refine ⟨s7, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7)))))), i7, ?_, ⟨hs, ?_, hl, hv⟩,
      ⟨hp.trans (args .rdi (by simp)), hn.trans (args .rsi (by simp)), trivial,
        hb.trans (args .rdx (by simp)), ?_⟩, ?_, ?_⟩
    · cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e7.rip
    · cases v <;> simpa [statePointer, Mode.stateOffset] using hd
    · exact ⟨by cases v <;> simpa [statePointer, Mode.stateOffset] using hr,
        hz.trans (args .rbp (by simp)), by intro _; exact ht.trans (args .r13 (by simp))⟩
    · simp
    · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7))))))).mono
      intro c hc
      simpa only [List.mem_append, or_self] using hc
  ·
    obtain ⟨s4, h4, i4, sp4, e4, o4, a4⟩ := setupAdvance
      (effect := movR64R64Effect (p + BitVec.ofNat 64 (9)) 12 4) hCall
      (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (9)) 0x49 0xe4 (by unfold RexWPrefix; decide) (by decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (9) (by cases v <;> decide +kernel))
      (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [movR64R64Effect, h.read_reg])
      (by
        intro c hc
        simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i3 sp3 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e3.rip) o3
    obtain ⟨s5, h5, i5, sp5, e5, o5, a5⟩ := setupAdvance
      (effect := leaR64Effect (p + BitVec.ofNat 64 (12)) 13 (.rip 0x49cd)) hCall
      (lea_r64_effect_step (p + BitVec.ofNat 64 (12)) 0x4c (by unfold RexWPrefix; decide) 5 (.rip 0x49cd) (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (12) (by cases v <;> decide +kernel))
      (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
      (by
        intro c hc
        simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i4 sp4 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e4.rip) o4
    obtain ⟨s6, h6, i6, sp6, e6, o6, a6⟩ := setupAdvance
      (effect := movR32Imm32Effect (p + BitVec.ofNat 64 (digestSetupTail v true)) 5 2 201) hCall
      (mov_r32_imm32_effect_step (p + BitVec.ofNat 64 (digestSetupTail v true)) 0xba (by decide) 201)
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (digestSetupTail v true) (by cases v <;> decide +kernel))
      (by intro t; simp [movR32Imm32Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [movR32Imm32Effect])
      (by
        intro c hc
        simp only [movR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i5 sp5 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e5.rip) o5
    obtain ⟨s7, h7, i7, sp7, e7, o7, a7⟩ := setupAdvance
      (effect := movR64R64Effect (p + BitVec.ofNat 64 (digestSetupTail v true + 5)) 7 12) hCall
      (mov_r64_r64_effect_step (p + BitVec.ofNat 64 (digestSetupTail v true + 5)) 0x4c 0xe7 (by unfold RexWPrefix; decide) (by decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (digestSetupTail v true + 5) (by cases v <;> decide +kernel))
      (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [movR64R64Effect, h.read_reg])
      (by
        intro c hc
        simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [setupChanges])
      i6 sp6 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e6.rip) o6
    obtain ⟨s8, h8, i8, sp8, e8, o8, a8⟩ := setupAdvance
      (effect := xorR32R32Effect (p + BitVec.ofNat 64 (digestSetupTail v true + 8)) 2 6 6) hCall
      (xor_r32_r32_effect_step (p + BitVec.ofNat 64 (digestSetupTail v true + 8)) 0xf6 (by decide))
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using image.slice (digestSetupTail v true + 8) (by cases v <;> decide +kernel))
      (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
      (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
      (by
        intro c hc
        simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [setupChanges])
      i7 sp7 (by cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e7.rip) o7
    have hs := (o8.read (Operand.reg 4 : Operand 64) trivial).symm
    have hd := (o8.read (Operand.reg 7 : Operand 64) trivial).symm
    have hl := (o8.read (Operand.reg 2 : Operand 64) trivial).symm
    have hv := (o8.read (Operand.reg 6 : Operand 64) trivial).symm
    have hp := (o8.read (Operand.reg 15 : Operand 64) trivial).symm
    have hn := (o8.read (Operand.reg 14 : Operand 64) trivial).symm
    have hb := (o8.read (Operand.reg 3 : Operand 64) trivial).symm
    have hr := (o8.read (Operand.reg 12 : Operand 64) trivial).symm
    have hz := (o8.read (Operand.reg 5 : Operand 64) trivial).symm
    have ht := (o8.read (Operand.reg 13 : Operand 64) trivial).symm
    x86_norm [movR64R64Effect, leaR64Effect, movR32Imm32Effect,
      xorR32R32Effect, BitVec.xor_self, plainStateAddr] at hs hd hl hv hp hn hb hr hz ht
    change (Operand.reg 4 : Operand 64).read s = frameBase initial v .digest keccak true at sp
    simp only [BitVec.ofNat_eq_ofNat] at sp
    rw [sp] at hs hd hr
    refine ⟨s8, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8))))))), i8, ?_, ⟨hs, ?_, hl, hv⟩,
      ⟨hp.trans (args .rdi (by simp)), hn.trans (args .rsi (by simp)), trivial,
        hb.trans (args .rdx (by simp)), ?_⟩, ?_, ?_⟩
    · cases v <;> simpa only [movR64R64Effect, leaR64Effect, movR32Imm32Effect, xorR32R32Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceDiv, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, digestSetupTail, plainStateAddr] using e8.rip
    · cases v <;> simpa [statePointer, Mode.stateOffset] using hd
    · exact ⟨by cases v <;> simpa [statePointer, Mode.stateOffset] using hr,
        hz.trans (args .rbp (by simp)), by simp⟩
    · intro _; simpa only [leaLen, AddrMode.tail, immBytes_length, Nat.reduceDiv, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ht
    · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8)))))))).mono
      intro c hc
      simpa only [List.mem_append, or_self] using hc

end Sha3.Proofs.Wrapper
