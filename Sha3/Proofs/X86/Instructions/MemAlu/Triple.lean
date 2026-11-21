import Sha3.Proofs.X86.Instructions.MemAlu.Step
import Sha3.Proofs.X86.Instructions.MemAlu.Encode
import X86Proofs.Instructions.MovLoad.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xorMREffect (p : BitVec 64) (len n : Nat) (src : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let r := (Operand.mem a : Operand n).read s ^^^ (Operand.reg src : Operand n).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand n), r⟩]
    flags := some (xorFlags r) }

def xorM8Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  let r := (Operand.mem a : Operand 8).read s ^^^ imm
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem a : Operand 8), r⟩]
    flags := some (xorFlags r) }

def cmpM8Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) :
      Operand 8).read s) imm)) }

@[simp] theorem xorMREffect_components (p : BitVec 64) (len n : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (xorMREffect p len n src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) (n / 8), .flags, .rip] := rfl

@[simp] theorem xorM8Imm8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : (xorM8Imm8Effect p len am imm s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 1, .flags, .rip] := by
  simp [xorM8Imm8Effect, Effect.components]

@[simp] theorem cmpM8Imm8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : (cmpM8Imm8Effect p len am imm s).components =
      [.flags, .rip] := rfl

theorem xor_m64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x31 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeRmwOutputs t (am.addrAt s (3 + am.tail.length))
        (xorSpec (oracleBit (dataAccess t "load").oracle)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read t) (src.read t)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have hr := hrex.rexPrefix
  have hstep := xor_m_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode hlow
    hw.readable
  simp only [scanContext_rex _ _ hr] at hstep
  exact hstep

theorem xor_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0x31 :: am.modrm reg :: am.tail))
      (xorMREffect p (3 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hw, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, xor_m64_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hw,
    ReadyToStep.afterStep_rmw h _ _ _ _ _ hw.low hw.tables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0x31 :: am.modrm reg :: am.tail))
      (Effect.post (xorMREffect p (3 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMREffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (xor_m64_r64_effect_step p rex hrex reg am hv hx hb)

theorem xor_m32_r32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0x31 :: am.modrm reg :: am.tail))
      (xorMREffect p (2 + am.tail.length) 32 (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_m_r_step s h [] (by simp) (by simp) 32 (.inr rfl) rfl rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0x31 :: am.modrm reg :: am.tail))
      (Effect.post (xorMREffect p (2 + am.tail.length) 32 (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMREffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (xor_m32_r32_effect_step p reg am hv hx hb)

theorem xor_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0x31 :: am.modrm reg :: am.tail))
      (xorMREffect p (3 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_m_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow
    hread
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0x31 :: am.modrm reg :: am.tail))
      (Effect.post (xorMREffect p (3 + am.tail.length) 32
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMREffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (xor_m32_r32_rex_effect_step p rex hrex reg am hv hx hb)

theorem xor_m8_r8_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0x30 :: am.modrm reg :: am.tail))
      (xorMREffect p (2 + am.tail.length) 8 (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_m8_r8_step s h [] (by simp) (by simp) rfl rfl rfl reg
    (.inr (gprNumber_low4 reg hreg)) am hv (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow
    hread
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (RmwPre p am 1 (2 + am.tail.length))
      (codeRange p (0x30 :: am.modrm reg :: am.tail))
      (Effect.post (xorMREffect p (2 + am.tail.length) 8 (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMREffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (xor_m8_r8_effect_step p reg hreg am hv hx hb)

theorem xor_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0x30 :: am.modrm reg :: am.tail))
      (xorMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_m8_r8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow
    hread
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (rex :: 0x30 :: am.modrm reg :: am.tail))
      (Effect.post (xorMREffect p (3 + am.tail.length) 8
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorMREffect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (xor_m8_r8_rex_effect_step p rex hr reg am hv hx hb)

theorem xor_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (xorM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := xor_m8_imm8_step s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) imm hcode.bytesAt hlow hread
  simp only [BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_m8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
      (Effect.post (xorM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [xorM8Imm8Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp; omega))
    (xor_m8_imm8_effect_step p am hv hx hb imm)

theorem cmp_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := cmp_m8_imm8_step s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) imm hcode.bytesAt hlow hread
  simp only [BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_m8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (Effect.post (cmpM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpM8Imm8Effect_components]; simp [Component.Covers]) _)
    (cmp_m8_imm8_effect_step p am hv hx hb imm)

theorem xor_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 8 (3 + am.tail.length)) (codeRange p (encodeXorM64R64 src am))
      (Effect.post (xorMREffect p (3 + am.tail.length) 64 (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := xor_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem xor_m32_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeXorM32R32 src am).length)
      (codeRange p (encodeXorM32R32 src am))
      (Effect.post (xorMREffect p (encodeXorM32R32 src am).length 32 (src.setWidth 5) am)) := by
  unfold encodeXorM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := xor_m32_r32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xor_m32_r32_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem xor_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 1 (encodeXorM8R8 src am).length)
      (codeRange p (encodeXorM8R8 src am))
      (Effect.post (xorMREffect p (encodeXorM8R8 src am).length 8 (src.setWidth 5) am)) := by
  unfold encodeXorM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := xor_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := xor_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem xor_m8_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (RmwPre p am 1 (3 + am.tail.length)) (codeRange p (encodeXorM8Imm8 am imm))
      (Effect.post (xorM8Imm8Effect p (3 + am.tail.length) am imm)) :=
  xor_m8_imm8_triple_of_bytes p am hv hx hb (UInt8.ofBitVec imm)

theorem cmp_m8_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (encodeCmpM8Imm8 am imm))
      (Effect.post (cmpM8Imm8Effect p (3 + am.tail.length) am imm)) :=
  cmp_m8_imm8_triple_of_bytes p am hv hx hb (UInt8.ofBitVec imm)

example : encodeXorM64R64 11 (.sib 4 none 0 (.d8 0xA8)) = [0x4C, 0x31, 0x5C, 0x24, 0xA8] := by
  decide

example : encodeXorM64R64 6 (.sib 4 none 0 (.d8 0x18)) = [0x48, 0x31, 0x74, 0x24, 0x18] := by
  decide

example : encodeXorM32R32 8 (.sib 4 (some 7) 0 (.d8 0x10)) = [0x44, 0x31, 0x44, 0x3C, 0x10] := by
  decide

example : encodeXorM32R32 7 (.sib 4 (some 6) 0 (.d8 0x10)) = [0x31, 0x7C, 0x34, 0x10] := by
  decide

example : encodeXorM8R8 7 (.sib 2 (some 0) 0 .none) = [0x40, 0x30, 0x3C, 0x02] := by decide

example : encodeXorM8R8 7 (.sib 1 (some 0) 0 .none) = [0x40, 0x30, 0x3C, 0x01] := by decide

example : encodeXorM8R8 1 (.sib 4 (some 0) 0 (.d32 0xF8)) =
    [0x30, 0x8C, 0x04, 0xF8, 0x00, 0x00, 0x00] := by decide

example : encodeXorM8Imm8 (.sib 4 (some 7) 0 (.d32 0xF8)) 0x80 =
    [0x80, 0xB4, 0x3C, 0xF8, 0x00, 0x00, 0x00, 0x80] := by decide

example : encodeCmpM8Imm8 (.sib 4 none 0 (.d32 0x1D1)) 1 =
    [0x80, 0xBC, 0x24, 0xD1, 0x01, 0x00, 0x00, 0x01] := by decide

end X86Proofs
