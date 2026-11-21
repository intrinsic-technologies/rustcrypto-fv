import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu.Step
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def addM32R32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := addSpec ((Operand.mem addr : Operand 32).read s)
    ((Operand.reg src : Operand 32).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 32), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

def addR32M32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := addSpec ((Operand.reg dst : Operand 32).read s)
    ((Operand.mem addr : Operand 32).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), out.1.setWidth 64⟩]
    flags := some (.ofStatusFlags out.2) }

def xorR32M32LegacyEffect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let len := 2 + am.tail.length
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := (Operand.reg dst : Operand 32).read s ^^^ (Operand.mem addr : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), out.setWidth 64⟩]
    flags := some (xorFlags out) }

theorem addM32R32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (addM32R32Effect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [addM32R32Effect, Effect.components]

theorem addR32M32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (addR32M32Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem xorR32M32LegacyEffect_components (p : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (xorR32M32LegacyEffect p dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem add_m32_r32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0x01 :: am.modrm reg :: am.tail))
      (addM32R32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := add_m_r_step s h [] (by simp) (by simp) 32 (.inr rfl) rfl rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (2 + am.tail.length))
      (codeRange p (0x01 :: am.modrm reg :: am.tail))
      (Effect.post (addM32R32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [addM32R32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp only [List.length_cons]; omega))
    (add_m32_r32_effect_step p reg am hv hx hb)

theorem add_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0x01 :: am.modrm reg :: am.tail))
      (addM32R32Effect p (3 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := add_m_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow
    hread
  simp only [scanContext_rex _ _ hr,
    show (rexContext s.DS rex.toBitVec).rex_r4 = 0 from rfl,
    show (rexContext s.DS rex.toBitVec).rex_r3 = rexR rex.toBitVec from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_m32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (rex :: 0x01 :: am.modrm reg :: am.tail))
      (Effect.post (addM32R32Effect p (3 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [addM32R32Effect_components]; exact mem_components_rmw _ _) hpre.code (by simp only [List.length_cons]; omega))
    (add_m32_r32_rex_effect_step p rex hrex reg am hv hx hb)

theorem add_r32_m32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x03 :: am.modrm reg :: am.tail))
      (addR32M32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := add_r_m_step s h [] (by simp) (by simp) 32 (.inr rfl) rfl rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow hread
  simp only [show (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4 = 0 from rfl,
    show (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 = 0 from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self32]
    simp only [addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_r32_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (rex :: 0x03 :: am.modrm reg :: am.tail))
      (addR32M32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hr := hrex.rexPrefix
  have hstep := add_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow hread
  simp only [scanContext_rex _ _ hr,
    show (rexContext s.DS rex.toBitVec).rex_r4 = 0 from rfl,
    show (rexContext s.DS rex.toBitVec).rex_r3 = rexR rex.toBitVec from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self32]
    simp only [addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem xor_r32_m32_legacy_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x33 :: am.modrm reg :: am.tail))
      (xorR32M32LegacyEffect p (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := xor_r_m_step s h [] (by simp) (by simp) 32 (.inr rfl) rfl rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow hread
  simp only [show (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4 = 0 from rfl,
    show (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 = 0 from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeOutputs_self32]
    simp only [xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

attribute [x86_compose] addM32R32Effect addR32M32Effect xorR32M32LegacyEffect

@[x86_local] theorem addM32R32Effect_local (p : BitVec 64) (len : Nat) (r : BitVec 5) (am : AddrMode) :
    Effect.Local (addM32R32Effect p len r am) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · rfl
  · dsimp only [addM32R32Effect]
    rw [AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · rfl
  · dsimp only [addM32R32Effect, Effect.flag]
    rw [AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro w hw
    simp only [addM32R32Effect, List.mem_singleton] at hw
    subst w
    exact (show 32 % 8 = 0 from rfl)

theorem load32Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (value : BitVec 32 → BitVec 32 → BitVec 32)
    (flags : BitVec 32 → BitVec 32 → StatusFlagsOutcome) :
    Effect.Local (fun s =>
      let a := (Operand.reg dst : Operand 32).read s
      let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
      { rip := p + BitVec.ofNat 64 len
        writes := [⟨(Operand.reg dst : Operand 64), (value a b).setWidth 64⟩]
        flags := some (flags a b) }) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · rfl
  · dsimp only
    rw [AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · rfl
  · dsimp only [Effect.flag]
    rw [AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rfl

@[x86_local] theorem addR32M32Effect_local (p : BitVec 64) (len : Nat) (r : BitVec 5)
    (am : AddrMode) : Effect.Local (addR32M32Effect p len r am) :=
  load32Effect_local p len r am (fun a b => (addSpec a b).1)
    (fun a b => .ofStatusFlags (addSpec a b).2)

@[x86_local] theorem xorR32M32LegacyEffect_local (p : BitVec 64) (r : BitVec 5)
    (am : AddrMode) : Effect.Local (xorR32M32LegacyEffect p r am) :=
  load32Effect_local p (2 + am.tail.length) r am (fun a b => a ^^^ b)
    (fun a b => xorFlags (a ^^^ b))

end Sha2.Proofs.Common.SHA256.Compression
