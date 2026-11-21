import Sha3.Proofs.Permutation.LoadStore.Rmw

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xor_m8_r8_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3
        reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x30 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t ↦
      writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand 8).read t) (src.read t)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) :=
  xor_m8_r8_step s h pre hpre hlen haddr hrex2 hlock reg hreg am hv hctx hcode hlow hread

theorem xor_m8_imm8_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 1) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t ↦
      writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand 8).read t) (imm.toBitVec.signExtend 8)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) :=
  xor_m8_imm8_step s h pre hpre hlen haddr hrex2 hlock am hv hctx imm hcode hlow hread

theorem xor_m8_r8_effect_step_of_readable [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePreReadable p (storeAddrAt p am (2 + am.tail.length)) 1)
      (codeRange p (0x30 :: am.modrm reg :: am.tail))
      (xorMREffect p (2 + am.tail.length) 8 (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨⟨hp, hread⟩, havoid⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_m8_r8_step_of_readable s h [] (by simp) (by simp) rfl rfl rfl reg
    (.inr (gprNumber_low4 reg hreg)) am hv (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow
    hread
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw_of_readable h _ _ _ _ _ havoid,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m8_r8_rex_effect_step_of_readable [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (rex :: 0x30 :: am.modrm reg :: am.tail))
      (xorMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  obtain ⟨⟨hp, hread⟩, havoid⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_m8_r8_step_of_readable s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow
    hread
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw_of_readable h _ _ _ _ _ havoid,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m8_imm8_effect_step_of_readable [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  obtain ⟨⟨hp, hread⟩, havoid⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp)
      (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := xor_m8_imm8_step_of_readable s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) imm hcode.bytesAt hlow hread
  simp only [BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw_of_readable h _ _ _ _ _ havoid,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m8_r8_encoded_effect_step_of_readable [Bindings] (p : BitVec 64) (src : BitVec 4)
    (am : AddrMode)
    (hv : am.Valid) :
    StepEffect (StorePreReadable p (storeAddrAt p am (encodeXorM8R8 src am).length) 1)
      (codeRange p (encodeXorM8R8 src am))
      (xorMREffect p (encodeXorM8R8 src am).length 8 (src.setWidth 5) am) := by
  unfold encodeXorM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := xor_m8_r8_effect_step_of_readable p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xor_m8_r8_rex_effect_step_of_readable p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

end X86Proofs
