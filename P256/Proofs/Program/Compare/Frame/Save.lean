import P256.Proofs.Program.Compare.Block
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

namespace P256.Proofs.Program.Compare.Frame

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program.Compare.Block

def saveBytes : List UInt8 :=
  [0x55, 0x48, 0x89, 0xe5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x83, 0xec, 0x10]

structure SavePre (s : RamState) : Prop where
  rip : s.RIP = 0x11c860
  writable : ∀ back ∈ [8, 16, 24, 32, 40],
    MemWritable s (stackPtr s - BitVec.ofNat 64 back) 8
  apart : ∀ back ∈ [8, 16, 24, 32, 40],
    RangeApart (stackPtr s - BitVec.ofNat 64 back) 8 0x11c860 15

def saveEffect (s : RamState) : Effect :=
  { rip := 0x11c86f
    writes := [
      ⟨.mem (stackPtr s - 8), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 16), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 24), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 32), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 40), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨.reg 5, stackPtr s - 8⟩,
      ⟨.reg 4, stackPtr s - 56⟩]
    flags := some (.ofStatusFlags (subSpec (stackPtr s - 40) (16 : BitVec 64)).2) }

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

private theorem component_mem_beq_reg (a : BitVec 64) (n : Nat) (r : BitVec 5) :
    (Component.mem a n == Component.reg r) = false := rfl

private theorem component_reg_beq_mem (r : BitVec 5) (a : BitVec 64) (n : Nat) :
    (Component.reg r == Component.mem a n) = false := rfl

attribute [local x86_compose] component_mem_beq_reg component_reg_beq_mem

private theorem pushR64Effect_local (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    Effect.Local (pushR64Effect p len src) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro s t h
    simp only [pushR64Effect, pushEffect, pushAddr, stackPtr_read, h.read_reg]
  · intro s t h i hi
    exact congrArg some hi
  · intro s
    simp [pushR64Effect, pushEffect, Write.Full, Operand.Full]

private theorem subR64Imm8Effect_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (subR64Imm8Effect p dst imm) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro s t h
    simp only [subR64Imm8Effect, h.read_reg]
  · intro s t h i hi
    simp only [Effect.flag, subR64Imm8Effect, h.read_reg]
  · intro s
    simp [subR64Imm8Effect, Write.Full, Operand.Full]

attribute [local x86_local] pushR64Effect_local subR64Imm8Effect_local
attribute [local x86_compose] pushR64Effect pushEffect pushAddr stackPtr_read subR64Imm8Effect
  BitVec.sub_eq_add_neg BitVec.add_assoc

private theorem SavePre.apart_slice {s : RamState} (h : SavePre s)
    {back offset len : Nat} (hb : back ∈ [8, 16, 24, 32, 40])
    (hlen : offset + len ≤ 15) :
    RangeApart (stackPtr s - BitVec.ofNat 64 back) 8
      (0x11c860 + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply h.apart back hb i hi (offset + j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem push_pre_after {s t : RamState} {e : Effect} {p : BitVec 64}
    {len back : Nat} (h : e.Holds s t) (ho : Obs (e.after s true) t)
    (hp : e.rip = p) (hsp : pushAddr (e.after s true) = stackPtr s - BitVec.ofNat 64 back)
    (hw : MemWritable s (stackPtr s - BitVec.ofNat 64 back) 8)
    (hc : RangeApart (stackPtr s - BitVec.ofNat 64 back) 8 p len) :
    PushPre p len t := by
  have ha : pushAddr t = stackPtr s - BitVec.ofNat 64 back := by
    rw [pushAddr, stackPtr_read, ← ho.read_reg, ← stackPtr_read]
    exact hsp
  exact ⟨h.rip.trans hp, ha ▸ hw.of_holds h, ha ▸ hc⟩

private theorem push_avoids {s t : RamState} {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {back : Nat} (h : SavePre s)
    (hb : back ∈ [8, 16, 24, 32, 40])
    (hsp : pushAddr t = stackPtr s - BitVec.ofNat 64 back) :
    (pushR64Effect p len src t).Avoids (codeRange 0x11c860 saveBytes) := by
  intro x hx c hc hcov
  simp only [pushR64Effect, pushEffect_components, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcov
  · obtain ⟨j, hj, he⟩ := exists_of_mem_codeRange hx
    obtain ⟨i, hi, hxi⟩ := hcov
    apply h.apart back hb i hi j hj
    rw [← he, hxi, hsp]
  · exact hcov

def savePrefixEffect (s : RamState) : Effect :=
  { rip := 0x11c868
    writes := [⟨.mem (stackPtr s - 8), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 16), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨.mem (stackPtr s - 24), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨.reg 5, stackPtr s - 8⟩, ⟨.reg 4, stackPtr s - 24⟩] }

attribute [local x86_compose] savePrefixEffect

set_option maxRecDepth 2048 in
theorem save_prefix [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : BitVec 64, 0x11c860 ≤ ip.toNat → ip.toNat ≤ 0x11c86f →
      ip ≠ boundary.rip) :
    AdvancesBlock boundary SavePre (codeRange 0x11c860 saveBytes) savePrefixEffect := by
  have h₀ : StepEffect (PushPre (0x11c860 + 0) 1)
      (codeRange (0x11c860 + 0) [0x55])
      (pushR64Effect (0x11c860 + 0) 1 5) := push_r64_effect_step (0x11c860 : BitVec 64) 0x55 (by decide +kernel)
  have hMov : StepEffect (fun s ↦ s.RIP = (0x11c860 + 1))
      (codeRange (0x11c860 + 1) [0x48, 0x89, 0xe5])
      (movR64R64Effect (0x11c860 + 1) 5 4) := mov_r64_r64_effect_step (0x11c860 + 1 : BitVec 64) 0x48 0xe5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  have h₁ : StepEffect (PushPre (0x11c860 + 4) 2)
      (codeRange (0x11c860 + 4) [0x41, 0x57])
      (pushR64Effect (0x11c860 + 4) 2 15) := push_r64_rex_effect_step (0x11c860 + 4 : BitVec 64) 0x41 0x57
    (by unfold RexPrefix; decide +kernel) (by decide +kernel)
  have h₂ : StepEffect (PushPre (0x11c860 + 6) 2)
      (codeRange (0x11c860 + 6) [0x41, 0x56])
      (pushR64Effect (0x11c860 + 6) 2 14) := push_r64_rex_effect_step (0x11c860 + 6 : BitVec 64) 0x41 0x56
    (by unfold RexPrefix; decide +kernel) (by decide +kernel)
  p256_memcmp_block_begin h₀
  p256_memcmp_block_then hMov
  p256_memcmp_block_then h₁
  p256_memcmp_block_then h₂
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [savePrefixEffect]
  · x86_norm [savePrefixEffect]
  · intro i
    cases i <;> x86_norm [savePrefixEffect]
  · x86_norm [savePrefixEffect]
  all_goals first
    | (intro s hP
       exact ⟨hP.rip, hP.writable 8 (by simp),
         hP.apart_slice (back := 8) (offset := 0) (by simp) (by decide)⟩)
    | (intro s hP; exact push_avoids hP (back := 8) (by simp) rfl)
    | (intro s hP
       apply outside
       all_goals dsimp only [pushR64Effect, pushEffect, subR64Imm8Effect, movR64R64Effect]
       all_goals decide +kernel)
    | (intro s t hP hH hO
       first
       | (refine ⟨push_pre_after hH (hO true) (back := 16) (by x86_norm) (by x86_norm)
            (hP.writable 16 (by simp))
            (hP.apart_slice (back := 16) (offset := 4) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 16) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm)
       | (refine ⟨push_pre_after hH (hO true) (back := 24) (by x86_norm) (by x86_norm)
            (hP.writable 24 (by simp))
            (hP.apart_slice (back := 24) (offset := 6) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 24) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm)
       | (refine ⟨push_pre_after hH (hO true) (back := 32) (by x86_norm) (by x86_norm)
            (hP.writable 32 (by simp))
            (hP.apart_slice (back := 32) (offset := 8) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 32) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm)
       | (refine ⟨push_pre_after hH (hO true) (back := 40) (by x86_norm) (by x86_norm)
            (hP.writable 40 (by simp))
            (hP.apart_slice (back := 40) (offset := 10) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 40) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm))


set_option maxRecDepth 2048 in
theorem save [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : BitVec 64, 0x11c860 ≤ ip.toNat → ip.toNat ≤ 0x11c86f →
      ip ≠ boundary.rip) :
    AdvancesBlock boundary SavePre (codeRange 0x11c860 saveBytes) saveEffect := by
  have h₃ : StepEffect (PushPre (0x11c860 + 8) 2)
      (codeRange (0x11c860 + 8) [0x41, 0x54])
      (pushR64Effect (0x11c860 + 8) 2 12) := push_r64_rex_effect_step (0x11c860 + 8 : BitVec 64) 0x41 0x54
    (by unfold RexPrefix; decide +kernel) (by decide +kernel)
  have h₄ : StepEffect (PushPre (0x11c860 + 10) 1)
      (codeRange (0x11c860 + 10) [0x53])
      (pushR64Effect (0x11c860 + 10) 1 3) := push_r64_effect_step (0x11c860 + 10 : BitVec 64) 0x53 (by decide +kernel)
  have h₅ : StepEffect (fun s ↦ s.RIP = (0x11c860 + 11))
      (codeRange (0x11c860 + 11) [0x48, 0x83, 0xec, 0x10])
      (subR64Imm8Effect (0x11c860 + 11) 4 16) := sub_r64_imm8_effect_step (0x11c860 + 11 : BitVec 64) 0x48 0xec 16
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  suffices continuation : AdvancesBlock boundary SavePre (codeRange 0x11c860 saveBytes)
      savePrefixEffect → AdvancesBlock boundary SavePre (codeRange 0x11c860 saveBytes)
        saveEffect from continuation (save_prefix boundary outside)
  p256_memcmp_block_then h₃
  p256_memcmp_block_then h₄
  p256_memcmp_block_then h₅
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [saveEffect, savePrefixEffect]
  · x86_norm [saveEffect, savePrefixEffect]
  · intro i
    cases i <;> x86_norm [saveEffect, savePrefixEffect]
  · x86_norm [saveEffect, savePrefixEffect]
  all_goals first
    | (intro s hP
       exact ⟨hP.rip, hP.writable 8 (by simp),
         hP.apart_slice (back := 8) (offset := 0) (by simp) (by decide)⟩)
    | (intro s hP; exact push_avoids hP (back := 8) (by simp) rfl)
    | (intro s hP
       apply outside
       all_goals dsimp only [pushR64Effect, pushEffect, subR64Imm8Effect, movR64R64Effect]
       all_goals decide +kernel)
    | (intro s t hP hH hO
       first
       | (refine ⟨push_pre_after hH (hO true) (back := 16) (by x86_norm [savePrefixEffect]) (by x86_norm [savePrefixEffect])
            (hP.writable 16 (by simp))
            (hP.apart_slice (back := 16) (offset := 4) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 16) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm)
       | (refine ⟨push_pre_after hH (hO true) (back := 24) (by x86_norm [savePrefixEffect]) (by x86_norm [savePrefixEffect])
            (hP.writable 24 (by simp))
            (hP.apart_slice (back := 24) (offset := 6) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 24) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm)
       | (refine ⟨push_pre_after hH (hO true) (back := 32) (by x86_norm [savePrefixEffect]) (by x86_norm [savePrefixEffect])
            (hP.writable 32 (by simp))
            (hP.apart_slice (back := 32) (offset := 8) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 32) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm)
       | (refine ⟨push_pre_after hH (hO true) (back := 40) (by x86_norm [savePrefixEffect]) (by x86_norm [savePrefixEffect])
            (hP.writable 40 (by simp))
            (hP.apart_slice (back := 40) (offset := 10) (by simp) (by decide)), ?_⟩
          apply push_avoids hP (back := 40) (by simp)
          rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
          x86_norm [savePrefixEffect]))

end P256.Proofs.Program.Compare.Frame
