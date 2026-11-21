import ChaCha20Poly1305.Proofs.DecryptInPlace.Regions

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt
open ChaCha20Poly1305.Proofs.Wrapper
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

variable [b : Bindings] {s u v : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

private theorem keyWordSource (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (track : GTrack (prefixChanges s) s u) (i : Fin 4) :
    let a := s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)
    MemReadable u a 8 ∧ wd u a = (Detached.keyQuads key)[i] := by
  let k := s.regValue .rdi
  have valid : ValidInput s (registerRegion s .rdi 32) (key : ByteArray) := hc.inputsInMemory.1
  have low : k.toNat + 32 < 2^32 := valid.1
  have readable : Readable s.external k 32 := by
    have h := Readable.of_hasBytes valid.2 valid.1
    rw [show (key : ByteArray).size = 32 from key.size_toArray] at h
    simpa only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  have hi := i.isLt
  refine ⟨key_readable track.agrees.grow low readable.present _ (by omega), ?_⟩
  have sep := readStackApart hc (r := registerRegion s .rdi 32)
    (by simp [readRegions, decryptInPlace, inputRegion]) (by change 0 < 32; decide)
  change k.toNat + 32 ≤ (stackPtr s).toNat - 1072 ∨ (stackPtr s).toNat + 8 ≤ k.toNat at sep
  have floor := stackFloor hc
  have addr : (k + BitVec.ofNat 64 (8 * i.val)).toNat = k.toNat + 8 * i.val := by bv_omega
  have frame := widenToScratch hc (d := 32) (by decide)
    (trackedFrame (Nat.le_trans (by decide : 32 ≤ 1072) floor) track.agrees
      (by simp [prefixChanges, Component.isMem]))
  change memLoad u.external (k + BitVec.ofNat 64 (8 * i.val)) 64 = _
  rw [frame.memLoad_eq (a := k + BitVec.ofNat 64 (8 * i.val)) (k := 64) ⟨?_, ?_⟩]
  · change _ = (Vector.ofFn fun j : Fin 4 => Detached.pair key j)[i.val]
    rw [Vector.getElem_ofFn]
    exact Detached.pairAt (Detached.bytesOfRegion valid.2) i (by omega)
  · rw [addr]
    omega
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ + 8 ≤ (stackPtr s).toNat - 1072 ∨ (stackPtr s).toNat - 1072 + 1072 ≤ _
    rw [addr]
    omega

private theorem loadKeyWord (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (track : GTrack (prefixChanges s) s u) {p : BitVec 64} {bytes : List UInt8}
    {dst : BitVec 5} {am : AddrMode} (i : Fin 4)
    (step : StepEffect (LoadPre p (fun t => am.addr t (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p bytes) (movR64M64Effect p dst am))
    (code : CodeIn (codeRange p bytes) u) (rip : u.RIP = p)
    (addr : ∀ x, am.addr u x = s.regValue .rdi + BitVec.ofNat 64 (8 * i.val))
    (next : p + BitVec.ofNat 64 (movLoadLen am) ≠ (returnBoundary s).rip)
    (reg : Component.reg dst ∈ prefixChanges s) :
    ∃ v, Advances (returnBoundary s) 1 u v ∧ GTrack (prefixChanges s) s v ∧
      v.RIP = p + BitVec.ofNat 64 (movLoadLen am) ∧ rd v dst = (Detached.keyQuads key)[i] ∧
      AgreesExcept [.reg dst, .rip] u v := by
  obtain ⟨readable, word⟩ := keyWordSource hc track i
  obtain ⟨v, adv, tracked, effect⟩ := gtrack_step step track code
    ⟨rip, by rw [addr]; exact readable⟩ next (by
      simp only [Fits, movR64M64Effect_components, List.forall_mem_cons, List.not_mem_nil,
        false_implies, implies_true, and_true]
      exact ⟨.inl ⟨rfl, reg⟩, .inl ⟨rfl, by simp [prefixChanges]⟩⟩)
  refine ⟨v, adv, tracked, effect.rip, ?_, ?_⟩
  · have wr := effect.writes
    simp only [movR64M64Effect, addr] at wr
    exact wr.trans word
  · simpa only [movR64M64Effect_components] using effect.agrees

private theorem storeKeyWord (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (track : GTrack (prefixChanges s) s u) {off : Nat} {bytes : List UInt8}
    {src : BitVec 5} {am : AddrMode} {d : Nat} (lo : 8 ≤ d) (hi : d ≤ 32)
    (step : StepEffect
      (StorePre (BitVec.ofNat 64 (0x100000 + off)) (3 + am.tail.length)
        (storeAddrAt (BitVec.ofNat 64 (0x100000 + off)) am ((3 + am.tail.length))) 8)
      (codeRange (BitVec.ofNat 64 (0x100000 + off)) bytes)
      (movM64R64Effect (BitVec.ofNat 64 (0x100000 + off)) src am))
    (code : CodeIn (codeRange (BitVec.ofNat 64 (0x100000 + off)) bytes) u)
    (rip : u.RIP = BitVec.ofNat 64 (0x100000 + off))
    (addr : ∀ x, am.addr u x = stackPtr s - BitVec.ofNat 64 d)
    (inText : off + (3 + am.tail.length) < 11759) :
    ∃ v, Advances (returnBoundary s) 1 u v ∧ GTrack (prefixChanges s) s v ∧
      v.RIP = BitVec.ofNat 64 (0x100000 + off) + BitVec.ofNat 64 ((3 + am.tail.length)) ∧
      wd v (stackPtr s - BitVec.ofNat 64 d) = rd u src ∧
      AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 d) 8, .rip] u v := by
  have away : RangeApart (stackPtr s - BitVec.ofNat 64 d) 8
      (BitVec.ofNat 64 (0x100000 + off)) (3 + am.tail.length) := by
    intro i hi' j hj eq
    exact slotOutsideProgram hc lo (by omega) ⟨i, hi', rfl⟩
      (eq ▸ code_inProgram off _ (by omega) j hj)
  have next : BitVec.ofNat 64 (0x100000 + off) + BitVec.ofNat 64 ((3 + am.tail.length)) ≠
      (returnBoundary s).rip := by
    rw [← BitVec.ofNat_add, Nat.add_assoc]
    exact code_ne_boundary (boundaryOutside hc) _ inText
  obtain ⟨v, adv, tracked, effect⟩ := gtrack_step step track code
    ⟨rip, by simpa only [storeAddrAt, addr] using
      slotWritable hc lo (by omega : d ≤ 1072) track.agrees.grow,
      by simpa only [storeAddrAt, addr] using away⟩ next (by
        fits [prefixChanges, addr]
        exact .inr ⟨rfl, slotWriteValid hc (cap := 32) (by simp)
          lo hi (by decide)⟩)
  refine ⟨v, adv, tracked, effect.rip, ?_, ?_⟩
  · rw [← addr (BitVec.ofNat 64 (0x100000 + off) + BitVec.ofNat 64 ((3 + am.tail.length)))]
    exact effect.writes
  · simpa only [movM64R64Effect_components, storeAddrAt, addr] using effect.agrees

omit b in
private theorem otherKeySlot {d e : Nat} (separate : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d ≤ 32) (he : e ≤ 32)
    (agree : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 d) 8, .rip] u v) :
    wd v (stackPtr s - BitVec.ofNat 64 e) = wd u (stackPtr s - BitVec.ofNat 64 e) := by
  apply gload agree
  intro c hc i hi
  rcases List.mem_cons.mp hc with rfl | hc
  · exact slot_not_covers hi separate.symm (by omega) (by omega)
  · obtain rfl := List.mem_singleton.mp hc
    exact fun h => h

private theorem copyKey (hb : MachineRamUnitStrideDecodable b s)
    (hm : SupportedIntegerMachineState b.processor s)
    (hc : ValidCall decryptInPlace s [key, nonce, aad, msg]) :
    ∃ n v, Advances (returnBoundary s) n s v ∧ GTrack (prefixChanges s) s v ∧
      v.RIP = 0x101677 ∧ stackPtr v = stackPtr s - 72 ∧ keyCopy s v key := by
  have entry := entry_ready b hb hm hc.programLoaded
  have t0 : GTrack (prefixChanges s) s s := ⟨entry.ready, entry.code, AgreesExcept.refl _ _⟩
  have outside := boundaryOutside hc
  obtain ⟨v1, a1, t1, e1⟩ := gtrack_step
    (sub_r64_imm8_effect_step 0x101650 0x48 0xec 0x48 (by decide) (by decide) (by decide))
    t0 (program_text_slice t0.code 0x1650 4 (by decide +kernel)) hc.atEntryPoint
    (code_ne_boundary outside 0x1654 (by decide)) (by fits [prefixChanges])
  have sp1 : stackPtr v1 = stackPtr s - 72 := e1.writes
  have source {w : RamState} (agree : rd w 7 = rd s 7) : rd w 7 = s.regValue .rdi :=
    agree.trans (regValue_read s).1.symm
  have rdi1 := source (e1.agrees.read (by simp; decide))
  obtain ⟨v2, a2, t2, ip2, rax2, g2⟩ := loadKeyWord hc t1 (3 : Fin 4)
    (mov_r64_m64_effect_step 0x101654 0x48 (by decide) 0 (.base 7 (.d8 0x18))
      (by decide) (by decide) (by decide))
    (program_text_slice t1.code 0x1654 4 (by decide +kernel)) e1.rip
    (rdi_addr rdi1 0x18 24 rfl) (code_ne_boundary outside 0x1658 (by decide))
    (by simp [prefixChanges]; decide)
  have sp2 := sp_keep g2 (by decide) sp1
  obtain ⟨v3, a3, t3, ip3, word3, g3⟩ := storeKeyWord hc t2 (off := 0x1658)
    (d := 8) (by decide) (by decide)
    (mov_m64_r64_effect_step 0x101658 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40))
      (by decide) (by decide) (by decide))
    (program_text_slice t2.code 0x1658 5 (by decide +kernel)) ip2
    (rsp_addr sp2 0x40 64 rfl (by decide)) (by decide)
  have sp3 := sp_keep g3 (by simp) sp2
  have rdi3 : rd v3 7 = s.regValue .rdi :=
    ((g2.trans g3).read (by simp; decide) : rd v3 7 = rd v1 7).trans rdi1
  obtain ⟨v4, a4, t4, ip4, rax4, g4⟩ := loadKeyWord hc t3 (2 : Fin 4)
    (mov_r64_m64_effect_step 0x10165d 0x48 (by decide) 0 (.base 7 (.d8 0x10))
      (by decide) (by decide) (by decide))
    (program_text_slice t3.code 0x165d 4 (by decide +kernel)) ip3
    (rdi_addr rdi3 0x10 16 rfl) (code_ne_boundary outside 0x1661 (by decide))
    (by simp [prefixChanges]; decide)
  have sp4 := sp_keep g4 (by decide) sp3
  obtain ⟨v5, a5, t5, ip5, word2, g5⟩ := storeKeyWord hc t4 (off := 0x1661)
    (d := 16) (by decide) (by decide)
    (mov_m64_r64_effect_step 0x101661 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38))
      (by decide) (by decide) (by decide))
    (program_text_slice t4.code 0x1661 5 (by decide +kernel)) ip4
    (rsp_addr sp4 0x38 56 rfl (by decide)) (by decide)
  have sp5 := sp_keep g5 (by simp) sp4
  have rdi5 : rd v5 7 = s.regValue .rdi :=
    ((g4.trans g5).read (by simp; decide) : rd v5 7 = rd v3 7).trans rdi3
  obtain ⟨v6, a6, t6, ip6, rax6, g6⟩ := loadKeyWord hc t5 (0 : Fin 4)
    (mov_r64_m64_effect_step 0x101666 0x48 (by decide) 0 (.base 7 .none)
      (by decide) (by decide) (by decide))
    (program_text_slice t5.code 0x1666 3 (by decide +kernel)) ip5
    (rdi_addr0 rdi5) (code_ne_boundary outside 0x1669 (by decide))
    (by simp [prefixChanges]; decide)
  have sp6 := sp_keep g6 (by decide) sp5
  have rdi6 : rd v6 7 = s.regValue .rdi :=
    (g6.read (by decide) : rd v6 7 = rd v5 7).trans rdi5
  obtain ⟨v7, a7, t7, ip7, rdi7, g7⟩ := loadKeyWord hc t6 (1 : Fin 4)
    (mov_r64_m64_effect_step 0x101669 0x48 (by decide) 7 (.base 7 (.d8 0x8))
      (by decide) (by decide) (by decide))
    (program_text_slice t6.code 0x1669 4 (by decide +kernel)) ip6
    (rdi_addr rdi6 0x8 8 rfl) (code_ne_boundary outside 0x166d (by decide))
    (by simp [prefixChanges]; decide)
  have sp7 := sp_keep g7 (by decide) sp6
  obtain ⟨v8, a8, t8, ip8, word1, g8⟩ := storeKeyWord hc t7 (off := 0x166d)
    (d := 24) (by decide) (by decide)
    (mov_m64_r64_effect_step 0x10166d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30))
      (by decide) (by decide) (by decide))
    (program_text_slice t7.code 0x166d 5 (by decide +kernel)) ip7
    (rsp_addr sp7 0x30 48 rfl (by decide)) (by decide)
  have sp8 := sp_keep g8 (by simp) sp7
  obtain ⟨v9, a9, t9, ip9, word0, g9⟩ := storeKeyWord hc t8 (off := 0x1672)
    (d := 32) (by decide) (by decide)
    (mov_m64_r64_effect_step 0x101672 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28))
      (by decide) (by decide) (by decide))
    (program_text_slice t8.code 0x1672 5 (by decide +kernel)) ip8
    (rsp_addr sp8 0x28 40 rfl (by decide)) (by decide)
  refine ⟨_, v9, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans
    (a6.trans (a7.trans (a8.trans a9))))))), t9, ip9, sp_keep g9 (by simp) sp8, ?_⟩
  have keep3 := mem_keep g4 (by decide)
  have keep5 := mem_keep (g6.trans g7) (by decide)
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have hi := i.isLt
    have hval : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hval with h | h | h | h
    · exact .inl (Fin.ext h)
    · exact .inr (.inl (Fin.ext h))
    · exact .inr (.inr (.inl (Fin.ext h)))
    · exact .inr (.inr (.inr (Fin.ext h)))
  change wd v9 (stackPtr s - BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * i.val)) = _
  rw [sub_add_ofNat (stackPtr s) (show 8 * i.val ≤ 32 by have := i.isLt; omega)]
  rcases cases with rfl | rfl | rfl | rfl
  · exact word0.trans (((g7.trans g8).read (by simp; decide) : rd v8 0 = rd v6 0).trans rax6)
  · exact (otherKeySlot (e := 24) (by decide) (by decide) (by decide) g9).trans
      (word1.trans rdi7)
  · exact (otherKeySlot (e := 16) (by decide) (by decide) (by decide) g9).trans
      ((otherKeySlot (e := 16) (by decide) (by decide) (by decide) g8).trans
        ((keep5 _).trans (word2.trans rax4)))
  · exact (otherKeySlot (e := 8) (by decide) (by decide) (by decide) g9).trans
      ((otherKeySlot (e := 8) (by decide) (by decide) (by decide) g8).trans
        ((keep5 _).trans ((otherKeySlot (e := 8) (by decide) (by decide) (by decide) g5).trans
          ((keep3 _).trans (word3.trans rax2)))))

theorem lengthBranch (hb : MachineRamUnitStrideDecodable b s) (hm : SupportedIntegerMachineState b.processor s)
    (hc : ValidCall decryptInPlace s [key, nonce, aad, msg]) :
    ∃ n u, Advances (returnBoundary s) n s u ∧ AfterLength s u key msg.size := by
  obtain ⟨n, v, adv, tracked, ip, sp, keys⟩ := copyKey hb hm hc
  have outside := boundaryOutside hc
  obtain ⟨v1, a1, t1, e1⟩ := gtrack_step (mov_r32_imm32_effect_step 0x101677 0xb8 (by decide) 1)
    tracked (program_text_slice tracked.code 0x1677 5 (by decide +kernel)) ip
    (code_ne_boundary outside 0x167c (by decide)) (by fits [prefixChanges])
  obtain ⟨v2, a2, t2, e2⟩ := gtrack_step
    (cmp_r64_imm8_effect_step 0x10167c 0x49 0xf9 0x10 (by decide) (by decide) (by decide))
    t1 (program_text_slice t1.code 0x167c 4 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x1680 (by decide)) (by fits [prefixChanges, cmpR64Imm8Effect_components])
  have flag : (StatusFlags.ofRFLAGS v2.RFLAGS).CF = decide (msg.size < 16) := by
    have f := e2.flags
    change (cmpR64Imm8Effect 0x10167c 9 0x10 v1).FlagsHold v2 at f
    simp only [cmpR64Imm8Effect, Effect.FlagsHold, StatusFlagsOutcome.ofStatusFlags,
      StatusFlagsOutcome.Allows, FlagAllows] at f
    rw [f.1]
    change decide ((rd v1 9).toNat < 16) = _
    rw [show rd v1 9 = rd s 9 from t1.agrees.read (by simp [prefixChanges])]
    change decide ((s.regValue .r9).toNat < 16) = _
    have size : (s.regValue .r9).toNat = msg.size := hc.lengthArgumentsMatchInputs.2.2.2.1
    rw [size]
  have target : branchTarget 0x101680 2 ((0x3c : BitVec 8).signExtend 64) = 0x1016be := by decide
  have branch : (jccEffect 0x101680 2 2 ((0x3c : BitVec 8).signExtend 64) v2).rip =
      if msg.size < 16 then 0x1016be else 0x101682 := by
    simp only [jccEffect, branchEffect, condHolds_2, flag, target, decide_eq_true_eq]
    rfl
  obtain ⟨v3, a3, t3, e3⟩ := gtrack_step (jcc_rel8_effect_step 0x101680 2 0x3c)
    t2 (program_text_slice t2.code 0x1680 2 (by decide +kernel))
    ⟨e2.rip, fun _ => by rw [target]; decide⟩
    (by
      rw [branch]
      split
      · exact code_ne_boundary outside 0x16be (by decide)
      · exact code_ne_boundary outside 0x1682 (by decide))
    (by fits [prefixChanges])
  have ag := (e1.agrees.trans e2.agrees).trans e3.agrees
  refine ⟨_, v3, adv.trans (a1.trans (a2.trans a3)), t3, e3.rip.trans branch,
    sp_keep ag (by simp [jccEffect]; decide) sp, ?_, ?_⟩
  · change rd v3 0 = 1
    rw [show rd v3 0 = rd v1 0 from (e2.agrees.trans e3.agrees).read (by simp [jccEffect])]
    exact e1.writes
  · intro i
    exact (mem_keep ag (by simp [jccEffect, Component.isMem]) _).trans (keys i)

end ChaCha20Poly1305.Proofs.DecryptInPlace
