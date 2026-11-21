import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.MachineInvariant
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Memory
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Nop

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

set_option maxRecDepth 10000 in
theorem decode_push_contains {initial s : RamState} {input : List UInt8} {capacity used i : Nat}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (hu : used = 8 ∨ used = 16)
    (ha : pushAddr s = initial.regValue .rsp - BitVec.ofNat 64 used) (hi : i < 8) :
    (Stack.region initial 144).Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
  have hn : 144 ≤ (initial.regValue .rsp).toNat := by exact hv.stack.2.2.1
  have hb := hv.stack.1
  have hb' : (Stack.region initial 144).Bounded := by simpa [decodeRoutine] using hb
  have haddr : pushAddr s + BitVec.ofNat 64 i =
      BitVec.ofNat 64 ((Stack.region initial 144).start + (144 - used + i)) := by
    rw [ha]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    · have hused : used < 2^64 := by rcases hu with rfl | rfl <;> omega
      rw [Nat.mod_eq_of_lt hused, Nat.mod_eq_of_lt (by omega : i < 2^64)]
      congr 1
      change (initial.regValue .rsp).toNat - used + i =
        (initial.regValue .rsp).toNat - 144 + (144 - used + i)
      rcases hu with rfl | rfl <;> omega
    · change used % 2^64 ≤ (initial.regValue .rsp).toNat
      rcases hu with rfl | rfl <;> omega
  rw [haddr]
  apply region_contains_offset hb'
  change 144 - used + i < (initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - 144)
  rcases hu with rfl | rfl <;> omega

set_option maxRecDepth 100000 in
theorem decode_pushPre_from_call {initial s : RamState} {input : List UInt8} {capacity used : Nat}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (hu : used = 8 ∨ used = 16)
    (ha : pushAddr s = initial.regValue .rsp - BitVec.ofNat 64 used)
    (hm : (Stack.region initial 144).Allocated s.external)
    (hp : InProgram s.RIP) (r : BitVec 5) :
    PushPre s.RIP 1 s ∧ (pushR64Effect s.RIP 1 r s).Avoids programImage := by
  have hn : 144 ≤ (initial.regValue .rsp).toNat := by exact hv.stack.2.2.1
  have hb : (Stack.region initial 144).Bounded := by simpa [decodeRoutine] using hv.stack.1
  have haddr : (pushAddr s).toNat = (initial.regValue .rsp).toNat - used := by
    rw [ha, BitVec.toNat_sub_of_le]
    · rcases hu with rfl | rfl <;> rfl
    · change used % 2^64 ≤ (initial.regValue .rsp).toNat
      rcases hu with rfl | rfl <;> omega
  have havoid := hv.separation.2.1 (Stack.region initial 144) (by simp [decodeRoutine])
  have hw : MemWritable s (pushAddr s) 8 := by
    apply regionWritable hb hm
    · intro a h; exact (not_or.mp (havoid a h)).2
    · rw [haddr]; change (initial.regValue .rsp).toNat - 144 ≤ _
      rcases hu with rfl | rfl <;> omega
    · rw [haddr]
      change (initial.regValue .rsp).toNat - used + 8 ≤
        (initial.regValue .rsp).toNat - 144 +
          ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - 144))
      rcases hu with rfl | rfl <;> omega
    · decide
    · rw [haddr]
      have halign : (initial.regValue .rsp).toNat % 16 = 8 := hv.stack.2.2.2
      rcases hu with rfl | rfl <;> omega
  have hc : ∀ i < 8, ¬ InProgram (pushAddr s + BitVec.ofNat 64 i) := by
    intro i hi
    exact (not_or.mp (havoid _ (decode_push_contains hv hu ha hi))).1
  constructor
  · refine ⟨rfl, hw, ?_⟩
    intro i hi j hj he
    have hj0 : j = 0 := by omega
    subst j
    apply hc i hi
    rw [he]
    exact (congrArg InProgram (BitVec.add_zero (s.RIP : BitVec 64))).mpr hp
  · intro x hx c hmem hcov
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, he⟩ := hcov
      exact hc i hi (he ▸ ⟨x.2, hx⟩)
    · exact hcov

theorem nop_dword_3_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0x1f, 0x00])
      (fun _ => nopEffect p 3) :=
  nop_m_effect_step p [] (by decide) (by decide)
    (.base 0 .none) ⟨by decide, fun _ => by decide⟩ rfl rfl

set_option maxRecDepth 100000 in
theorem decode_zero_counters [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 41#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ EntryReady programImage t ∧
      t.RIP = (decodeAddress alphabet) + 48#64 ∧
      AgreesExcept [.reg 6, .reg 0, .flags, .rip] s t ∧
      AddrMode.reg64 6 t = 0#64 ∧ AddrMode.reg64 0 t = 0#64 := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := advanceAtOffset (decodeAddress alphabet) 41
    (xor_r32_r32_effect_step ((decodeAddress alphabet) + 41#64) 0xf6 (by decide))
    he.ready he.code (by cases alphabet <;> decide +kernel) hp hret
    (by dsimp only [xorR32R32Effect, movR64R64Effect, popR64Effect, nopEffect, jmpEffect]; cases alphabet <;> exact ⟨0x31, by decide +kernel⟩)
    (xorR32R32Effect_avoids _ _ _ _ _ _)
  change (xorR32R32Effect ((decodeAddress alphabet) + 41#64) 2 6 6 s).Holds s u at hu
  have heu := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = (decodeAddress alphabet) + 43#64 := by cases alphabet <;> exact hu.rip
  obtain ⟨v, hav, hrv, hcv, hv⟩ := advanceAtOffset (decodeAddress alphabet) 43
    (xor_r32_r32_effect_step ((decodeAddress alphabet) + 43#64) 0xc0 (by decide))
    heu.ready heu.code (by cases alphabet <;> decide +kernel) hpu hret
    (by dsimp only [xorR32R32Effect, movR64R64Effect, popR64Effect, nopEffect, jmpEffect]; cases alphabet <;> exact ⟨0x0f, by decide +kernel⟩)
    (xorR32R32Effect_avoids _ _ _ _ _ _)
  change (xorR32R32Effect ((decodeAddress alphabet) + 43#64) 2 0 0 u).Holds u v at hv
  have hev := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter heu hrv hcv hv.agrees
  have hpv : v.RIP = (decodeAddress alphabet) + 45#64 := by cases alphabet <;> exact hv.rip
  obtain ⟨t, hat, hrt, hct, ht⟩ := advanceAtOffset (decodeAddress alphabet) 45
    (nop_dword_3_effect_step ((decodeAddress alphabet) + 45#64))
    hev.ready hev.code (by cases alphabet <;> decide +kernel) hpv hret
    (by dsimp only [xorR32R32Effect, movR64R64Effect, popR64Effect, nopEffect, jmpEffect]; cases alphabet <;> exact ⟨0x44, by decide +kernel⟩)
    (Effect.Avoids.of_noMem (by simp [Effect.components, nopEffect, Component.Covers]) _)
  have hfu : AgreesExcept [.reg 6, .flags, .rip] s u := by simpa using hu.agrees
  have hfv : AgreesExcept [.reg 0, .flags, .rip] u v := by simpa using hv.agrees
  have hft : AgreesExcept [.rip] v t := by simpa [Effect.components, nopEffect] using ht.agrees
  have hc : AddrMode.reg64 6 u = 0#64 := by
    have hw := hu.writes
    simpa [xorR32R32Effect, Write.AllHold, Operand.read, AddrMode.reg64] using hw
  have hs : AddrMode.reg64 0 v = 0#64 := by
    have hw := hv.writes
    simpa [xorR32R32Effect, Write.AllHold, Operand.read, AddrMode.reg64] using hw
  refine ⟨t, hau.trans (hav.trans hat),
    Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hev hrt hct ht.agrees, (by cases alphabet <;> exact ht.rip), ?_, ?_, ?_⟩
  · exact (hfu.trans (hfv.trans hft)).mono (by simp)
  · exact ((hfv.trans hft).read (by simp)).trans hc
  · exact (hft.read (by simp)).trans hs


set_option maxRecDepth 100000 in
theorem decode_initialize_loop [Bindings]
    {initial s : RamState} {input : List UInt8} {capacity : Nat} {boundary : ReturnBoundary}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 39#64)
    (hf : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial s)
    (hax : AddrMode.reg64 9 s = BitVec.ofNat 64 (input.length / 2))
    (hne : input ≠ []) (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ EntryReady programImage t ∧
      DecodeMachineLoopInvariant [alphabet] (decodeAddress alphabet) 228 initial input [] input
        #v[outputRegion initial (input.length / 2), Stack.region initial (decodeRoutine alphabet).minStackBytes]
        (decodeCallEffects initial (input.length / 2)) t := by
  have hsp : stackPtr s = initial.regValue .rsp := hf.read (r := 4) (n := 64) (by simp)
  have hm : s.external = initial.external := hf.external (by simp [Component.Covers])
  have hpa : pushAddr s = initial.regValue .rsp - 8#64 := by
    change stackPtr s - 8#64 = _
    rw [hsp]
  obtain ⟨hpre, havoid⟩ := decode_pushPre_from_call hv (Or.inl rfl) hpa
    (by rw [hm]; simpa [decodeRoutine] using hv.stack.2.1)
    (by rw [hp]; exact ⟨0x55, by cases alphabet <;> decide +kernel⟩) 5
  obtain ⟨u, hau, hru, hcu, hu⟩ := advanceInProgram
    (push_r64_effect_step (decodeAddress alphabet + 39#64) 0x55 (by decide))
    he.ready he.code (by cases alphabet <;> decide +kernel)
    (by simpa only [hp] using hpre) hret
    (by dsimp only [pushR64Effect, pushEffect]; cases alphabet <;> exact ⟨0x53, by decide +kernel⟩)
    (by simpa only [hp, show gprNumber 0 0 (opcodeReg 0x55) = 5 by decide +kernel] using havoid)
  change (pushR64Effect (decodeAddress alphabet + 39#64) 1 5 s).Holds s u at hu
  have heu := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = decodeAddress alphabet + 40#64 := by cases alphabet <;> exact hu.rip
  have hfu : AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s u := by simpa using hu.agrees
  have hpush : AddrMode.reg64 4 u = pushAddr s ∧
      memLoad u.external (pushAddr s) 64 = AddrMode.reg64 5 s := hu.writes
  have hpb : pushAddr u = initial.regValue .rsp - 16#64 := by
    change AddrMode.reg64 4 u - 8#64 = _
    rw [hpush.1, hpa, BitVec.sub_sub]
    rfl
  obtain ⟨hpreu, havoidu⟩ := decode_pushPre_from_call hv (Or.inr rfl) hpb
    (by intro a ha; exact Option.isSome_iff_exists.mp ((hf.trans hfu).grow a
          (Option.isSome_iff_exists.mpr (hv.stack.2.1 a (by simpa [decodeRoutine] using ha)))))
    (by rw [hpu]; exact ⟨0x53, by cases alphabet <;> decide +kernel⟩) 3
  obtain ⟨v, hav, hrv, hcv, hve⟩ := advanceInProgram
    (push_r64_effect_step (decodeAddress alphabet + 40#64) 0x53 (by decide))
    heu.ready heu.code (by cases alphabet <;> decide +kernel)
    (by simpa only [hpu] using hpreu) hret
    (by dsimp only [pushR64Effect, pushEffect]; cases alphabet <;> exact ⟨0x31, by decide +kernel⟩)
    (by simpa only [hpu, show gprNumber 0 0 (opcodeReg 0x53) = 3 by decide +kernel] using havoidu)
  change (pushR64Effect (decodeAddress alphabet + 40#64) 1 3 u).Holds u v at hve
  have hev := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter heu hrv hcv hve.agrees
  have hpv : v.RIP = decodeAddress alphabet + 41#64 := by cases alphabet <;> exact hve.rip
  have hfv : AgreesExcept [.reg 4, .mem (pushAddr u) 8, .rip] u v := by simpa using hve.agrees
  have hpushv : AddrMode.reg64 4 v = pushAddr u ∧
      memLoad v.external (pushAddr u) 64 = AddrMode.reg64 3 u := hve.writes
  obtain ⟨t, hat, het, hpt, hft, hsi, hcount⟩ := decode_zero_counters hev hpv hret
  have hfull := hf.trans (hfu.trans (hfv.trans hft))
  have hmem : t.external = v.external := hft.external (by simp [Component.Covers])
  have hspt : AddrMode.reg64 4 t = pushAddr u := (hft.read (by simp)).trans hpushv.1
  have hspt8 : AddrMode.reg64 4 t + 8#64 = pushAddr s := by
    rw [hspt]
    change AddrMode.reg64 4 u - 8#64 + 8#64 = _
    rw [BitVec.sub_add_cancel, hpush.1]
  have hwordbx : Machine.loadBytes t.external (AddrMode.reg64 4 t) 8 =
      .ok (AddrMode.reg64 3 initial) := by
    have hr : ∀ i < 8, (v.external[pushAddr u + BitVec.ofNat 64 i]?).isSome := by
      intro i hi; exact hfv.grow _ (hpreu.write.mem i hi)
    have hl := (Bytes.of_memLoad (n := 64) hr).loadBytes64
    rw [hpushv.2] at hl
    have hbx : AddrMode.reg64 3 u = AddrMode.reg64 3 initial := (hf.trans hfu).read (by simp)
    rw [hbx] at hl
    rw [hmem, hspt]
    exact hl
  have hwordbp : Machine.loadBytes t.external (AddrMode.reg64 4 t + 8#64) 8 =
      .ok (AddrMode.reg64 5 initial) := by
    have hr : ∀ i < 8, (u.external[pushAddr s + BitVec.ofNat 64 i]?).isSome := by
      intro i hi; exact hfu.grow _ (hpre.write.mem i hi)
    have hb := Bytes.of_memLoad (n := 64) hr
    rw [hpush.2, show AddrMode.reg64 5 s = AddrMode.reg64 5 initial from hf.read (by simp)] at hb
    have ha : RangeApart (pushAddr u) 8 (pushAddr s) 8 := by
      have hx : pushAddr s = pushAddr u + 8#64 := hspt8.symm.trans (congrArg (· + 8#64) hspt)
      rw [hx]
      simpa only [BitVec.add_zero] using RangeApart.offsets (pushAddr u)
        (a := 0) (b := 8) (len := 8) (count := 8) (by decide) (by decide) (Or.inl (by decide))
    have hb' := hb.of_agreesExcept hfv (by
      intro i hi c hc hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hcover
      · obtain ⟨j, hj, hjEq⟩ := hcover
        exact ha j hj i hi hjEq.symm
      · exact hcover)
    rw [hmem, hspt8]
    exact hb'.loadBytes64
  have hframe : MemoryWriteFrame initial t #v[Stack.region initial 144] := by
    apply hfull.memoryWriteFrame
    intro c hc x hcover
    have hc' : c = .mem (pushAddr s) 8 ∨ c = .mem (pushAddr u) 8 := by
      cases c <;> simp_all [Component.Covers]
    rcases hc' with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨_, by simp, decode_push_contains hv (Or.inl rfl) hpa hi⟩
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨_, by simp, decode_push_contains hv (Or.inr rfl) hpb hi⟩
  refine ⟨t, hau.trans (hav.trans hat), het, ?_⟩
  refine {
    split := rfl
    processedEven := rfl
    rip := by simpa only [ite_eq_right hne] using hpt
    rsi := by simpa [decodeLoop] using hsi
    rax := by simpa using hcount
    rdi := hfull.read (by simp)
    rcx := hfull.read (by simp)
    rdx := hfull.read (by simp)
    r9 := ((hfu.trans (hfv.trans hft)).read (by simp)).trans hax
    rsp := hspt.trans hpb
    savedRBX := hwordbx
    savedRBP := hwordbp
    output := by rfl
    inputUnchanged := ?_
    outputAllocated := ?_
    directionFlagUnset := hfull.directionFlagClear (by simp) hv.directionFlagUnset
    frame := ?_
    agrees := ?_
  }
  · intro i
    apply hframe _
    intro r hr
    simp only [Vector.mem_singleton] at hr
    subst r
    exact hv.separation.1 (0 : Fin 3) (2 : Fin 3) (by decide) _
      (region_contains_offset hv.inputInMemory.2.1 (by simpa only [inputRegion, registerRegion, List.size_toByteArray] using i.isLt))
  · rw [outputCapacity hv]
    intro a ha
    exact Option.isSome_iff_exists.mp (hfull.grow _
      (Option.isSome_iff_exists.mpr (hv.outputInMemory.2.2 a ha)))
  · intro a ha
    apply hframe a
    intro r hr
    simp only [Vector.mem_singleton] at hr
    subst r
    exact ha _ (by simp [decodeRoutine])
  · apply hfull.mono
    simp [decodeCallEffects, decodeLoopEffects, hpa, hpb]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
