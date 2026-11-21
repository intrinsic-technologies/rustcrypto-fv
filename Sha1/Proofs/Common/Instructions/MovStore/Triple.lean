import Sha1.Proofs.Common.Instructions.MovStore.Step
import Sha1.Proofs.Common.Instructions.Store
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple

namespace Sha1.Proofs.Common.Instructions.MovStore

open X86 X86.Machine X86.UserProcess X86Proofs

theorem mov_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp only [List.length_cons]; omega) (by omega) (by omega)) hw

theorem mov_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => Sha1.Proofs.Common.Instructions.Store.storeEffect_avoids (by simp only [List.length_cons]; omega) _ _ hpre)
    (mov_m64_r64_effect_step p rex hrex reg am hv hx hb)

theorem mov_m32_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp only [List.length_cons]; omega) (by omega) (by omega)) hw

theorem mov_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => Sha1.Proofs.Common.Instructions.Store.storeEffect_avoids (by simp only [List.length_cons]; omega) _ _ hpre)
    (mov_m32_r32_effect_step p rex hrex reg am hv hx hb)

theorem mov_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32Effect p am imm) :=
  Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_imm32_step s h rex hrex am hv hx hb imm hcode.bytesAt
        (hcode.low_len (by simp only [List.length_cons, List.length_append, immBytes_length]; omega) (by omega) (by omega)) hw

theorem mov_m64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM64Imm32Effect p am imm)) :=
  Triple.of_effect (fun _ hpre => Sha1.Proofs.Common.Instructions.Store.storeEffect_avoids (by simp only [List.length_cons, List.length_append, immBytes_length]; omega) _ _ hpre)
    (mov_m64_imm32_effect_step p rex hrex am hv hx hb imm)

theorem mov_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (encodeMovM64R64 src am)) (Effect.post (movM64R64Effect p (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := mov_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem mov_m64_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (encodeMovM64Imm32 am imm)) (Effect.post (movM64Imm32Effect p am imm)) := by
  obtain ⟨hrex, _, hx, hb⟩ := am.rexByte_true_spec 0
  exact mov_m64_imm32_triple_of_bytes p _ hrex am hv hx hb imm

theorem mov_m32_r32_low_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (movM32R32LowEffect p (gprNumber 0 0 reg)
        am) :=
  Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m_r_step s h [] (by simp)
        (by simp) 32 (.inr rfl)
        (by exact rfl)
        (by rfl) (by rfl)
        (by rfl) reg am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
        hcode.bytesAt hlow (by exact hw)
      dsimp only at hstep
      have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m32_r32_low_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32LowEffect p (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => Sha1.Proofs.Common.Instructions.Store.storeEffect_avoids (by simp only [List.length_cons]; omega) _ _ hpre)
    (mov_m32_r32_low_effect_step p reg am hv hx hb)

theorem mov_m32_imm32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (6 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32Effect p (6 + am.tail.length) am imm) := by
  refine Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons, List.length_append, immBytes_length]; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := mov_m_imm32_prefix_step s h [] (by simp)
    (by simp) 32 (.inr rfl) (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hw)
  simp only [movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (6 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => Sha1.Proofs.Common.Instructions.Store.storeEffect_avoids (by simp only [List.length_cons, List.length_append, immBytes_length]; omega) _ _ hpre)
    (mov_m32_imm32_effect_step p am hv hx hb imm)

theorem mov_m32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (7 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32Effect p (7 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  refine Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons, List.length_append, immBytes_length]; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := mov_m_imm32_prefix_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  simp only [scanContext_rex _ _ hr, movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (7 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => Sha1.Proofs.Common.Instructions.Store.storeEffect_avoids (by simp only [List.length_cons, List.length_append, immBytes_length]; omega) _ _ hpre)
    (mov_m32_imm32_rex_effect_step p rex hrex am hv hx hb imm)

end Sha1.Proofs.Common.Instructions.MovStore
