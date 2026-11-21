import P256.Proofs.Program.Compare.Block
import P256.Proofs.Program.Compare.Ranges
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace P256.Proofs.Program.Compare.Frame

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program.Compare.Block

abbrev word (s : RamState) (offset : BitVec 64) : BitVec 64 :=
  (Operand.mem (stackPtr s + offset) : Operand 64).read s

def restoreBytes : List UInt8 :=
  [0x48, 0x83, 0xc4, 0x10, 0x5b, 0x41, 0x5c,
   0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3]

abbrev restoreCode : CodeMap := codeRange 0x11c923 restoreBytes

def Outside (address : BitVec 64) : Prop :=
  address.toNat < 0x11c923 ∨ 0x11c92f < address.toNat

private theorem outside_ne {address pc : BitVec 64} (h : Outside address)
    (hlo : 0x11c923 ≤ pc.toNat) (hhi : pc.toNat ≤ 0x11c92f) : pc ≠ address := by
  intro he
  subst pc
  unfold Outside at h
  omega

private theorem pop_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (popR64Effect p len dst) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro t t' h
    have hs : stackPtr t = stackPtr t' := congrArg (fun g ↦ g[gprIndex 4]) h.gpr
    simp only [popR64Effect, hs, h.read_mem]
  · intro t t' _ i hi
    exact congrArg some hi
  · intro t
    simp [popR64Effect, Write.Full, Operand.Full]

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_local] pop_local
attribute [local x86_compose] popR64Effect stackPtr_read

structure RestorePre (s : RamState) : Prop where
  rip : s.RIP = 0x11c923
  read : MemReadable s (stackPtr s + 16) 48

def restoreEffect (s : RamState) : Effect :=
  { rip := 0x11c92f
    writes := [⟨.reg 3, word s 16⟩, ⟨.reg 12, word s 24⟩,
      ⟨.reg 14, word s 32⟩,
      ⟨.reg 15, word s 40⟩, ⟨.reg 5, word s 48⟩,
      ⟨.reg 4, stackPtr s + 56⟩]
    flags := some (.ofStatusFlags (addSpec (stackPtr s) 16).2) }

private theorem pop_pre {s t : RamState} {e : Effect} {p : BitVec 64}
    (h : e.Holds s t) (ho : Obs (e.after s true) t) (hp : e.rip = p)
    (hr : MemReadable s (stackPtr (e.after s true)) 8) : PopPre p t := by
  refine ⟨h.rip_of hp, ?_⟩
  have hs : stackPtr (e.after s true) = stackPtr t := ho.read_reg (n := 64) 4
  rw [← hs]
  exact hr.of_holds h

theorem restore [Bindings] (boundary : ReturnBoundary) (hOutside : Outside boundary.rip) :
    AdvancesBlock boundary RestorePre restoreCode restoreEffect := by
  have hAdd : StepEffect (fun s ↦ s.RIP = (0x11c923 + 0))
      (codeRange (0x11c923 + 0) [0x48, 0x83, 0xc4, 0x10])
      (addR64Imm8Effect (0x11c923 + 0) 4 16) :=
    add_r64_imm8_effect_step (0x11c923 + 0) 0x48 0xc4 16
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x11c923 + 4)) (codeRange (0x11c923 + 4) [0x5b])
      (popR64Effect (0x11c923 + 4) 1 3) :=
    pop_r64_effect_step (0x11c923 + 4) 0x5b (by decide) (by decide)
  have hPop1 : StepEffect (PopPre (0x11c923 + 5)) (codeRange (0x11c923 + 5) [0x41, 0x5c])
      (popR64Effect (0x11c923 + 5) 2 12) :=
    pop_r64_rex_effect_step (0x11c923 + 5) 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop3 : StepEffect (PopPre (0x11c923 + 7)) (codeRange (0x11c923 + 7) [0x41, 0x5e])
      (popR64Effect (0x11c923 + 7) 2 14) :=
    pop_r64_rex_effect_step (0x11c923 + 7) 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop4 : StepEffect (PopPre (0x11c923 + 9)) (codeRange (0x11c923 + 9) [0x41, 0x5f])
      (popR64Effect (0x11c923 + 9) 2 15) :=
    pop_r64_rex_effect_step (0x11c923 + 9) 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre (0x11c923 + 11)) (codeRange (0x11c923 + 11) [0x5d])
      (popR64Effect (0x11c923 + 11) 1 5) :=
    pop_r64_effect_step (0x11c923 + 11) 0x5d (by decide) (by decide)
  unfold restoreCode restoreBytes
  p256_memcmp_block_begin hAdd
  p256_memcmp_block_then hPop0
  p256_memcmp_block_then hPop1
  p256_memcmp_block_then hPop3
  p256_memcmp_block_then hPop4
  p256_memcmp_block_then hPop5
  p256_memcmp_block_finish [restoreEffect, word]
  all_goals first
    | (intro t _; dsimp only [popR64Effect, addR64Imm8Effect, movR64R64Effect]
       exact outside_ne hOutside (by decide +kernel) (by decide +kernel))
    | (intro s t hP hH hO
       refine ⟨pop_pre hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
       x86_norm
       first
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_zero] using
             P256.Proofs.Program.Compare.Ranges.memReadable_slice hP.read 0 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc] using
             P256.Proofs.Program.Compare.Ranges.memReadable_slice hP.read 8 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc] using
             P256.Proofs.Program.Compare.Ranges.memReadable_slice hP.read 16 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc] using
             P256.Proofs.Program.Compare.Ranges.memReadable_slice hP.read 24 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc] using
             P256.Proofs.Program.Compare.Ranges.memReadable_slice hP.read 32 8 (by decide +kernel))

def effect (s : RamState) : Effect :=
  { rip := word s 56
    writes := [⟨.reg 3, word s 16⟩, ⟨.reg 12, word s 24⟩,
      ⟨.reg 14, word s 32⟩,
      ⟨.reg 15, word s 40⟩, ⟨.reg 5, word s 48⟩,
      ⟨.reg 4, stackPtr s + 64⟩]
    flags := some (.ofStatusFlags (addSpec (stackPtr s) 16).2) }

private theorem ret_local : Effect.Local retEffect := by
  refine ⟨?_, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro t t' h
    have hs : stackPtr t = stackPtr t' := congrArg (fun g ↦ g[gprIndex 4]) h.gpr
    simp only [retEffect, stackTop, hs, h.read_mem]
  · intro t t' h
    have hs : stackPtr t = stackPtr t' := congrArg (fun g ↦ g[gprIndex 4]) h.gpr
    simp only [retEffect, hs]
  · intro t t' _ i hi
    exact congrArg some hi
  · intro t
    simp [retEffect, Write.Full, Operand.Full]

attribute [local x86_compose] retEffect stackTop

private theorem effect_of_restore_ret {s mid final : RamState}
    (hRestore : (restoreEffect s).Holds s mid)
    (hRet : (retEffect mid).Holds mid final) : (effect s).Holds s final := by
  have h := hRestore.seq ret_local (by simp [restoreEffect, Write.Full, Operand.Full]) hRet
  apply h.weaken
  · x86_norm [restoreEffect, effect, word]
  · x86_norm [restoreEffect, effect, word]
  · intro i; cases i <;> x86_norm [restoreEffect, effect, word]
  · x86_norm [restoreEffect, effect, word]

theorem restore_return [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn restoreCode s) (hPre : RestorePre s)
    (hOutside : Outside boundary.rip) (hLow : (word s 56).toNat < 2^32)
    (hDifferent : word s 56 ≠ boundary.rip ∨ stackPtr s + 64 ≠ boundary.rsp) :
    ∃ fuel final, Advances boundary fuel s final ∧ ReadyToStep final ∧
      CodeIn restoreCode final ∧ (effect s).Holds s final := by
  obtain ⟨fuel, mid, hAdvance, hMidReady, hMidCode, hRestore⟩ :=
    restore boundary hOutside s hReady hCode hPre
  have hMemory := hRestore.agrees.external
    (by simp [restoreEffect, Effect.components, Component.Covers])
  have hStack : stackPtr mid = stackPtr s + 56 := hRestore.writes.2.2.2.2.2
  have hTop : stackTop mid = word s 56 := by
    change (Operand.mem (stackPtr mid) : Operand 64).read mid = _
    rw [hStack]
    change memLoad mid.external (stackPtr s + 56) 64 = _
    rw [hMemory]
    rfl
  have hRead : MemReadable mid (stackPtr mid) 8 := by
    rw [hStack]
    apply MemReadable.of_holds hRestore
    simpa [BitVec.add_assoc] using
      P256.Proofs.Program.Compare.Ranges.memReadable_slice hPre.read 40 8 (by decide +kernel)
  obtain ⟨final, hStep, hFinalReady, hRet⟩ := ret_effect_step 0x11c92f mid hMidReady
    (hMidCode.mono (codeRange_mem_of_drop (p := 0x11c923) (all := restoreBytes)
      (bytes := [0xc3]) 12 (by decide +kernel)))
    ⟨⟨hRestore.rip, hRead⟩, hTop ▸ hLow⟩
  have hFinal := effect_of_restore_ret hRestore hRet
  refine ⟨fuel + 1, final, ?_, hFinalReady,
    hRet.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components mid) _) hMidCode,
    hFinal⟩
  apply hAdvance.trans (Advances.of_step hStep ?_)
  rcases hDifferent with hDifferent | hDifferent
  · exact .inl (by rw [hRet.rip]; change stackTop mid ≠ boundary.rip; rw [hTop]; exact hDifferent)
  · apply Or.inr
    change stackPtr final ≠ boundary.rsp
    have hs : stackPtr final = stackPtr s + 64 := hFinal.writes.2.2.2.2.2
    exact hs ▸ hDifferent

theorem effect_memory {s final : RamState} (h : (effect s).Holds s final) :
    final.external = s.external :=
  h.agrees.external (by simp [effect, Effect.components, Component.Covers])

theorem effect_eax {s final : RamState} (h : (effect s).Holds s final) :
    (Operand.reg 0 : Operand 32).read final = (Operand.reg 0 : Operand 32).read s :=
  h.agrees.read (by simp [effect, Effect.components])

theorem restore_return_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {image : CodeMap} (hReady : ReadyToStep s) (hCode : CodeIn image s)
    (hSlice : CodeIn restoreCode s) (hPre : RestorePre s)
    (hOutside : Outside boundary.rip) (hLow : (word s 56).toNat < 2^32)
    (hDifferent : word s 56 ≠ boundary.rip ∨ stackPtr s + 64 ≠ boundary.rsp) :
    ∃ fuel final, Advances boundary fuel s final ∧ ReadyToStep final ∧
      CodeIn image final ∧ (effect s).Holds s final := by
  obtain ⟨fuel, final, hAdvance, hFinalReady, _, hFinal⟩ :=
    restore_return hReady hSlice hPre hOutside hLow hDifferent
  exact ⟨fuel, final, hAdvance, hFinalReady,
    hFinal.codeIn (Effect.Avoids.of_noMem
      (by simp [effect, Effect.components, Component.Covers]) image) hCode, hFinal⟩

end P256.Proofs.Program.Compare.Frame
