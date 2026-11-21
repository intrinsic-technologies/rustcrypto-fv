import ChaCha20Poly1305.Proofs.DecryptInPlace.Regions

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt
open ChaCha20Poly1305.Proofs.Wrapper
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

variable [b : Bindings] {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

omit b in
private theorem prefixFits (hc : ValidCall decryptInPlace s [key, nonce, aad, msg]) :
    Fits (callChanges s) (prefixChanges s) := by
  fits [prefixChanges, callChanges]
  exact .inr ⟨rfl, slotWriteValid (cap := 80) (offset := 32) hc (by simp) (by decide) (by decide) (by decide)⟩

omit b in
private theorem callSlotPre (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    {cs : List Component} (ag : AgreesExcept cs s u) {p : BitVec 64} {size d : Nat}
    {addr : RamState → BitVec 64} (rip : u.RIP = p) (a : addr u = stackPtr s - BitVec.ofNat 64 d)
    (lo : 8 ≤ d) (hi : d ≤ 80) (code : ∀ j < size, InProgram (p + BitVec.ofNat 64 j)) :
    StorePre p size addr 8 u := by
  refine ⟨rip, a ▸ slotWritable hc lo (by omega) ag.grow, ?_⟩
  rw [a]
  intro i h j hj eq
  exact slotOutsideProgram hc lo (by omega : d ≤ 1072) (x := stackPtr s - BitVec.ofNat 64 d + BitVec.ofNat 64 i)
    ⟨i, h, rfl⟩ (eq.symm ▸ code j hj)

omit b in
private theorem tagReadable (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    {cs : List Component} (ag : AgreesExcept cs s u) {a : BitVec 64}
    (lo : (s.regValue .rcx).toNat ≤ a.toNat)
    (hi : a.toNat+8 ≤ (s.regValue .rcx).toNat+msg.size) : MemReadable u a 8 := by
  have valid : ValidInput s (registerRegion s .rcx msg.size) msg := hc.inputsInMemory.2.2.2.1
  have rd := Readable.of_hasBytes valid.2 valid.1
  change Readable s.external (BitVec.ofNat 64 (s.regValue .rcx).toNat) msg.size at rd
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at rd
  have r := rd.sub lo hi
  exact ⟨r.low, fun i h => ag.grow _ (r.present i h)⟩

omit b in
private theorem slotKept {cs : List Component} {sp : BitVec 64} {w k : Nat}
    {u v : RamState} (ag : AgreesExcept cs u v)
    (mem : ∀ c ∈ cs, c.isMem = false ∨ c = .mem (sp - BitVec.ofNat 64 w) 8)
    (sep : k+8 ≤ w ∨ w+8 ≤ k) (kw : k ≤ 1104) (ww : w ≤ 1104) :
    wd v (sp - BitVec.ofNat 64 k) = wd u (sp - BitVec.ofNat 64 k) := by
  apply gload ag
  intro c hc i hi
  rcases mem c hc with pure | rfl
  · exact nonmem_not_covers pure _
  · exact slot_not_covers hi sep kw ww

private theorem initTrack (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (start : AfterLength s u key msg.size) : GTrack (callChanges s) s u :=
  ⟨start.track.ready, start.track.code, (prefixFits hc).widen start.track.agrees⟩

set_option maxRecDepth 3000 in
set_option maxHeartbeats 650000 in
theorem callSetup (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32) (start : AfterLength s u key msg.size) :
    ∃ n v, Advances (returnBoundary s) n u v ∧
      AtDetached s v (inPlacePacket s key nonce aad msg long small) := by
  let p := inPlacePacket s key nonce aad msg long small
  have hOut := boundaryOutside hc
  have T0 := initTrack hc start
  have capMem : Component.mem (stackPtr s - 80) 80 ∈ callChanges s := by simp [callChanges]
  have rip0 : u.RIP = 0x101682 := by simpa only [ite_eq_right (Nat.not_lt.mpr long)] using start.rip
  have sp0 := start.rsp
  have base0 : rd u 1 = p.buf := start.track.agrees.read (by simp [prefixChanges])
  have sizeArg : (s.regValue .r9).toNat = msg.size := hc.lengthArgumentsMatchInputs.2.2.2.1
  have size0 : rd u 9 = s.regValue .r9 := start.track.agrees.read (by simp [prefixChanges])
  have aad0 : rd u 8 = s.regValue .r8 := start.track.agrees.read (by simp [prefixChanges])
  have cut : s.regValue .r9 - 16 = p.n := by
    change _ = BitVec.ofNat 64 (msg.size-16)
    bv_omega
  have low : p.buf.toNat+msg.size < 2^32 := hc.inputsInMemory.2.2.2.1.1
  have nNat : p.n.toNat = msg.size-16 := Nat.mod_eq_of_lt (by omega)
  have fr := trackedFrame (Nat.le_trans (by decide : 32 ≤ 1072) (stackFloor hc)) start.track.agrees
    (by simp [prefixChanges, Component.isMem])
  have tags := (ciphertextParts hc long small (widenToScratch hc (by decide) fr)).2
  have addr1 : ∀ x, (AddrMode.base 9 (.d8 0xf0)).addr u x = p.n := by
      intro x
      change rd u 9 + 18446744073709551600 = _
      rw [size0]
      bv_omega
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
      (lea_r64_effect_step 0x101682 0x49 (by decide) 7
        (AddrMode.base 9 (.d8 0xf0)) (by decide) (by decide) (by decide))
      T0 (program_text_slice T0.code 0x1682 4 (by decide +kernel))
      rip0 (code_ne_boundary hOut 0x1686 (by decide)) (by fits [callChanges, leaR64Effect_components])
  change (leaR64Effect 0x101682 7 (AddrMode.base 9 (.d8 0xf0)) u).Holds u u1 at e1
  have ag1 : AgreesExcept [.reg 7, .rip] u u1 := e1.agrees
  have reg1 {r : BitVec 5} (h : r ≠ 7) : rd u1 r = rd u r := ag1.read (by simpa using h)
  have sp1 := sp_keep ag1 (by simp) sp0
  have mem1 (x : BitVec 64) : wd u1 x = wd u x := mem_keep ag1 (by simp [Component.isMem]) x
  have cipherLen : rd u1 7 = p.n := (show rd u1 7 = _ from e1.writes).trans (addr1 0x101686)
  have base1 : rd u1 1 = p.buf := by simp (disch := decide) only [reg1]; exact base0
  have size1 : rd u1 9 = s.regValue .r9 := by simp (disch := decide) only [reg1]; exact size0
  have addr2 : ∀ x, (AddrMode.sib 1 (some 9) 0 (.d8 0xf0)).addr u1 x = p.buf+p.n := by
      intro x
      change rd u1 1 + (rd u1 9 <<< 0) + 18446744073709551600 = _
      rw [base1, size1, BitVec.shiftLeft_zero]
      bv_omega
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
      (mov_r64_m64_effect_step 0x101686 0x4a (by decide) 0
        (AddrMode.sib 1 (some 9) 0 (.d8 0xf0)) (by decide) (by decide) (by decide))
      T1 (program_text_slice T1.code 0x1686 5 (by decide +kernel))
      ⟨e1.rip, by
          rw [addr2]
          apply tagReadable hc T1.agrees
          · change p.buf.toNat ≤ _; bv_omega
          · change _ ≤ p.buf.toNat+msg.size; bv_omega⟩ (code_ne_boundary hOut 0x168b (by decide)) (by fits [callChanges])
  change (movR64M64Effect 0x101686 0 (AddrMode.sib 1 (some 9) 0 (.d8 0xf0)) u1).Holds u1 u2 at e2
  have ag2 : AgreesExcept [.reg 0, .rip] u1 u2 := e2.agrees
  have reg2 {r : BitVec 5} (h : r ≠ 0) : rd u2 r = rd u1 r := ag2.read (by simpa using h)
  have sp2 := sp_keep ag2 (by simp) sp1
  have mem2 (x : BitVec 64) : wd u2 x = wd u1 x := mem_keep ag2 (by simp [Component.isMem]) x
  have tagLow : rd u2 0 = p.tag.extractLsb' 0 64 := by
      have h : rd u2 0 = wd u1 ((AddrMode.sib 1 (some 9) 0 (.d8 0xf0)).addr u1 0x10168b) := e2.writes
      rw [h, addr2, mem1]
      exact tags.1
  have base2 : rd u2 1 = p.buf := by simp (disch := decide) only [reg2, reg1]; exact base0
  have size2 : rd u2 9 = s.regValue .r9 := by simp (disch := decide) only [reg2, reg1]; exact size0
  have addr3 : ∀ x, (AddrMode.sib 1 (some 9) 0 (.d8 0xf8)).addr u2 x = p.buf+p.n+8 := by
      intro x
      change rd u2 1 + (rd u2 9 <<< 0) + 18446744073709551608 = _
      rw [base2, size2, BitVec.shiftLeft_zero]
      bv_omega
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
      (mov_r64_m64_effect_step 0x10168b 0x4e (by decide) 1
        (AddrMode.sib 1 (some 9) 0 (.d8 0xf8)) (by decide) (by decide) (by decide))
      T2 (program_text_slice T2.code 0x168b 5 (by decide +kernel))
      ⟨e2.rip, by
          rw [addr3]
          apply tagReadable hc T2.agrees
          · change p.buf.toNat ≤ _; bv_omega
          · change _ ≤ p.buf.toNat+msg.size; bv_omega⟩ (code_ne_boundary hOut 0x1690 (by decide)) (by fits [callChanges])
  change (movR64M64Effect 0x10168b 9 (AddrMode.sib 1 (some 9) 0 (.d8 0xf8)) u2).Holds u2 u3 at e3
  have ag3 : AgreesExcept [.reg 9, .rip] u2 u3 := e3.agrees
  have reg3 {r : BitVec 5} (h : r ≠ 9) : rd u3 r = rd u2 r := ag3.read (by simpa using h)
  have sp3 := sp_keep ag3 (by simp) sp2
  have mem3 (x : BitVec 64) : wd u3 x = wd u2 x := mem_keep ag3 (by simp [Component.isMem]) x
  have tagHigh : rd u3 9 = p.tag.extractLsb' 64 64 := by
      have h : rd u3 9 = wd u2 ((AddrMode.sib 1 (some 9) 0 (.d8 0xf8)).addr u2 0x101690) := e3.writes
      rw [h, addr3, mem2, mem1]
      exact tags.2

  have addr4 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x10)).addr u3 x = stackPtr s - BitVec.ofNat 64 56 := rsp_addr (k := 72) sp3 0x10 16 rfl (by decide)
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
      (mov_m64_r64_effect_step 0x101690 0x48 (by decide) 1
        (AddrMode.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
      T3 (program_text_slice T3.code 0x1690 5 (by decide +kernel))
      (callSlotPre (d := 56) hc T3.agrees e3.rip (addr4 0x101695) (by decide) (by decide)
        (code_inProgram 0x1690 5 (by decide))) (code_ne_boundary hOut 0x1695 (by decide)) (by
        fits [callChanges, addr4]
        exact .inr ⟨rfl, slotWriteValid (offset := 56) (cap := 80) hc capMem (by decide) (by decide) (by decide)⟩)
  change (movM64R64Effect 0x101690 1 (AddrMode.sib 4 none 0 (.d8 0x10)) u3).Holds u3 u4 at e4
  have ag4 : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 56) 8, .rip] u3 u4 := by
      simpa only [movM64R64Effect_components, storeAddrAt, addr4] using e4.agrees
  have reg4 (r : BitVec 5) : rd u4 r = rd u3 r := ag4.read (by simp)
  have sp4 := sp_keep ag4 (by simp) sp3
  have mem4 {k : Nat} (h : k+8 ≤ 56 ∨ 56+8 ≤ k) (hk : k ≤ 1104) :=
      slotKept (sp := stackPtr s) (w := 56) ag4 (by simp [Component.isMem]) h hk (by decide)
  have srcSlot : wd u4 (stackPtr s - BitVec.ofNat 64 56) = p.buf := by
      have h : wd u4 ((AddrMode.sib 4 none 0 (.d8 0x10)).addr u3 0x101695) = rd u3 1 := e4.writes
      rw [addr4] at h
      exact h.trans (by simp (disch := decide) only [reg3, reg2, reg1]; exact base0)
  have addr5 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x18)).addr u4 x = stackPtr s - BitVec.ofNat 64 48 := rsp_addr (k := 72) sp4 0x18 24 rfl (by decide)
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
      (mov_m64_r64_effect_step 0x101695 0x48 (by decide) 1
        (AddrMode.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
      T4 (program_text_slice T4.code 0x1695 5 (by decide +kernel))
      (callSlotPre (d := 48) hc T4.agrees e4.rip (addr5 0x10169a) (by decide) (by decide)
        (code_inProgram 0x1695 5 (by decide))) (code_ne_boundary hOut 0x169a (by decide)) (by
        fits [callChanges, addr5]
        exact .inr ⟨rfl, slotWriteValid (offset := 48) (cap := 80) hc capMem (by decide) (by decide) (by decide)⟩)
  change (movM64R64Effect 0x101695 1 (AddrMode.sib 4 none 0 (.d8 0x18)) u4).Holds u4 u5 at e5
  have ag5 : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u4 u5 := by
      simpa only [movM64R64Effect_components, storeAddrAt, addr5] using e5.agrees
  have reg5 (r : BitVec 5) : rd u5 r = rd u4 r := ag5.read (by simp)
  have sp5 := sp_keep ag5 (by simp) sp4
  have mem5 {k : Nat} (h : k+8 ≤ 48 ∨ 48+8 ≤ k) (hk : k ≤ 1104) :=
      slotKept (sp := stackPtr s) (w := 48) ag5 (by simp [Component.isMem]) h hk (by decide)
  have dstSlot : wd u5 (stackPtr s - BitVec.ofNat 64 48) = p.buf := by
      have h : wd u5 ((AddrMode.sib 4 none 0 (.d8 0x18)).addr u4 0x10169a) = rd u4 1 := e5.writes
      rw [addr5] at h
      exact h.trans (by simp (disch := decide) only [reg4, reg3, reg2, reg1]; exact base0)
  have addr6 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x20)).addr u5 x = stackPtr s - BitVec.ofNat 64 40 := rsp_addr (k := 72) sp5 0x20 32 rfl (by decide)
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step
      (mov_m64_r64_effect_step 0x10169a 0x48 (by decide) 7
        (AddrMode.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
      T5 (program_text_slice T5.code 0x169a 5 (by decide +kernel))
      (callSlotPre (d := 40) hc T5.agrees e5.rip (addr6 0x10169f) (by decide) (by decide)
        (code_inProgram 0x169a 5 (by decide))) (code_ne_boundary hOut 0x169f (by decide)) (by
        fits [callChanges, addr6]
        exact .inr ⟨rfl, slotWriteValid (offset := 40) (cap := 80) hc capMem (by decide) (by decide) (by decide)⟩)
  change (movM64R64Effect 0x10169a 7 (AddrMode.sib 4 none 0 (.d8 0x20)) u5).Holds u5 u6 at e6
  have ag6 : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 40) 8, .rip] u5 u6 := by
      simpa only [movM64R64Effect_components, storeAddrAt, addr6] using e6.agrees
  have reg6 (r : BitVec 5) : rd u6 r = rd u5 r := ag6.read (by simp)
  have sp6 := sp_keep ag6 (by simp) sp5
  have mem6 {k : Nat} (h : k+8 ≤ 40 ∨ 40+8 ≤ k) (hk : k ≤ 1104) :=
      slotKept (sp := stackPtr s) (w := 40) ag6 (by simp [Component.isMem]) h hk (by decide)
  have lengthSlot : wd u6 (stackPtr s - BitVec.ofNat 64 40) = p.n := by
      have h : wd u6 ((AddrMode.sib 4 none 0 (.d8 0x20)).addr u5 0x10169f) = rd u5 7 := e6.writes
      rw [addr6] at h
      exact h.trans (by simp (disch := decide) only [reg5, reg4, reg3, reg2]; exact cipherLen)
  have addr7 : ∀ x, (AddrMode.sib 4 none 0 .none).addr u6 x = stackPtr s - BitVec.ofNat 64 72 := rsp_addr0 (k := 72) sp6
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step
      (mov_m64_r64_effect_step 0x10169f 0x4c (by decide) 1
        (AddrMode.sib 4 none 0 .none) (by decide) (by decide) (by decide))
      T6 (program_text_slice T6.code 0x169f 4 (by decide +kernel))
      (callSlotPre (d := 72) hc T6.agrees e6.rip (addr7 0x1016a3) (by decide) (by decide)
        (code_inProgram 0x169f 4 (by decide))) (code_ne_boundary hOut 0x16a3 (by decide)) (by
        fits [callChanges, addr7]
        exact .inr ⟨rfl, slotWriteValid (offset := 72) (cap := 80) hc capMem (by decide) (by decide) (by decide)⟩)
  change (movM64R64Effect 0x10169f 9 (AddrMode.sib 4 none 0 .none) u6).Holds u6 u7 at e7
  have ag7 : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 72) 8, .rip] u6 u7 := by
      simpa only [movM64R64Effect_components, storeAddrAt, addr7] using e7.agrees
  have reg7 (r : BitVec 5) : rd u7 r = rd u6 r := ag7.read (by simp)
  have sp7 := sp_keep ag7 (by simp) sp6
  have mem7 {k : Nat} (h : k+8 ≤ 72 ∨ 72+8 ≤ k) (hk : k ≤ 1104) :=
      slotKept (sp := stackPtr s) (w := 72) ag7 (by simp [Component.isMem]) h hk (by decide)
  have tagSlot : wd u7 (stackPtr s - BitVec.ofNat 64 72) = p.tag.extractLsb' 64 64 := by
      have h : wd u7 ((AddrMode.sib 4 none 0 .none).addr u6 0x1016a3) = rd u6 9 := e7.writes
      rw [addr7] at h
      exact h.trans (by simp (disch := decide) only [reg6, reg5, reg4]; exact tagHigh)

  have addr8 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x28)).addr u7 x = stackPtr s - BitVec.ofNat 64 32 := rsp_addr (k := 72) sp7 0x28 40 rfl (by decide)
  obtain ⟨u8, a8, T8, e8⟩ := gtrack_step
      (lea_r64_effect_step 0x1016a3 0x48 (by decide) 7
        (AddrMode.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
      T7 (program_text_slice T7.code 0x16a3 5 (by decide +kernel))
      e7.rip (code_ne_boundary hOut 0x16a8 (by decide)) (by fits [callChanges, leaR64Effect_components])
  change (leaR64Effect 0x1016a3 7 (AddrMode.sib 4 none 0 (.d8 0x28)) u7).Holds u7 u8 at e8
  have ag8 : AgreesExcept [.reg 7, .rip] u7 u8 := e8.agrees
  have reg8 {r : BitVec 5} (h : r ≠ 7) : rd u8 r = rd u7 r := ag8.read (by simpa using h)
  have sp8 := sp_keep ag8 (by simp) sp7
  have mem8 (x : BitVec 64) : wd u8 x = wd u7 x := mem_keep ag8 (by simp [Component.isMem]) x
  have keyArg : rd u8 7 = stackPtr s - BitVec.ofNat 64 32 := (show rd u8 7 = _ from e8.writes).trans (addr8 0x1016a8)
  have addr9 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x10)).addr u8 x = stackPtr s - BitVec.ofNat 64 56 := rsp_addr (k := 72) sp8 0x10 16 rfl (by decide)
  obtain ⟨u9, a9, T9, e9⟩ := gtrack_step
      (lea_r64_effect_step 0x1016a8 0x4c (by decide) 1
        (AddrMode.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
      T8 (program_text_slice T8.code 0x16a8 5 (by decide +kernel))
      e8.rip (code_ne_boundary hOut 0x16ad (by decide)) (by fits [callChanges, leaR64Effect_components])
  change (leaR64Effect 0x1016a8 9 (AddrMode.sib 4 none 0 (.d8 0x10)) u8).Holds u8 u9 at e9
  have ag9 : AgreesExcept [.reg 9, .rip] u8 u9 := e9.agrees
  have reg9 {r : BitVec 5} (h : r ≠ 9) : rd u9 r = rd u8 r := ag9.read (by simpa using h)
  have sp9 := sp_keep ag9 (by simp) sp8
  have mem9 (x : BitVec 64) : wd u9 x = wd u8 x := mem_keep ag9 (by simp [Component.isMem]) x
  have descriptorAddr : rd u9 9 = stackPtr s - BitVec.ofNat 64 56 := (show rd u9 9 = _ from e9.writes).trans (addr9 0x1016ad)
  obtain ⟨u10, a10, T10, e10⟩ := gtrack_step
      (mov_r64_r64_effect_step 0x1016ad 0x4c 0xc1 (by decide) (by decide))
      T9 (program_text_slice T9.code 0x16ad 3 (by decide +kernel))
      e9.rip (code_ne_boundary hOut 0x16b0 (by decide)) (by fits [callChanges])
  change (movR64R64Effect 0x1016ad 1 8 u9).Holds u9 u10 at e10
  have ag10 : AgreesExcept [.reg 1, .rip] u9 u10 := e10.agrees
  have reg10 {r : BitVec 5} (h : r ≠ 1) : rd u10 r = rd u9 r := ag10.read (by simpa using h)
  have sp10 := sp_keep ag10 (by simp) sp9
  have mem10 (x : BitVec 64) : wd u10 x = wd u9 x := mem_keep ag10 (by simp [Component.isMem]) x
  have aadLengthArg : rd u10 1 = s.regValue .r8 :=
      (show rd u10 1 = rd u9 8 from e10.writes).trans (by simp (disch := decide) only [reg9, reg8, reg7, reg6, reg5, reg4, reg3, reg2, reg1]; exact aad0)
  obtain ⟨u11, a11, T11, e11⟩ := gtrack_step
      (mov_r64_r64_effect_step 0x1016b0 0x4d 0xc8 (by decide) (by decide))
      T10 (program_text_slice T10.code 0x16b0 3 (by decide +kernel))
      e10.rip (code_ne_boundary hOut 0x16b3 (by decide)) (by fits [callChanges])
  change (movR64R64Effect 0x1016b0 8 9 u10).Holds u10 u11 at e11
  have ag11 : AgreesExcept [.reg 8, .rip] u10 u11 := e11.agrees
  have reg11 {r : BitVec 5} (h : r ≠ 8) : rd u11 r = rd u10 r := ag11.read (by simpa using h)
  have sp11 := sp_keep ag11 (by simp) sp10
  have mem11 (x : BitVec 64) : wd u11 x = wd u10 x := mem_keep ag11 (by simp [Component.isMem]) x
  have descriptorArg : rd u11 8 = stackPtr s - 56 :=
      (show rd u11 8 = rd u10 9 from e11.writes).trans (by simp (disch := decide) only [reg10]; exact descriptorAddr)
  obtain ⟨u12, a12, T12, e12⟩ := gtrack_step
      (mov_r64_r64_effect_step 0x1016b3 0x49 0xc1 (by decide) (by decide))
      T11 (program_text_slice T11.code 0x16b3 3 (by decide +kernel))
      e11.rip (code_ne_boundary hOut 0x16b6 (by decide)) (by fits [callChanges])
  change (movR64R64Effect 0x1016b3 9 0 u11).Holds u11 u12 at e12
  have ag12 : AgreesExcept [.reg 9, .rip] u11 u12 := e12.agrees
  have reg12 {r : BitVec 5} (h : r ≠ 9) : rd u12 r = rd u11 r := ag12.read (by simpa using h)
  have sp12 := sp_keep ag12 (by simp) sp11
  have mem12 (x : BitVec 64) : wd u12 x = wd u11 x := mem_keep ag12 (by simp [Component.isMem]) x
  have tagArg : rd u12 9 = p.tag.extractLsb' 0 64 :=
      (show rd u12 9 = rd u11 0 from e12.writes).trans (by simp (disch := decide) only [reg11, reg10, reg9, reg8, reg7, reg6, reg5, reg4, reg3]; exact tagLow)

  have addr13 : pushAddr u12 = stackPtr s - BitVec.ofNat 64 80 := by rw [pushAddr, sp12]; exact sub_sub_ofNat _ 72 8
  obtain ⟨u13, a13, T13, e13⟩ := gtrack_step
      (call_rel32_effect_step 0x1016b6 0xffffeb35 (by decide))
      T12 (program_text_slice T12.code 0x16b6 5 (by decide +kernel))
      (callSlotPre (d := 80) hc T12.agrees e12.rip addr13 (by decide) (by decide)
        (code_inProgram 0x16b6 5 (by decide))) (code_ne_boundary hOut 0x1f0 (by decide)) (by
        fits [callChanges, callEffect, pushEffect_components, addr13]
        exact .inr ⟨rfl, slotWriteValid (offset := 80) (cap := 80) hc capMem (by decide) (by decide) (by decide)⟩)
  change (callEffect (fun _ => branchTarget 0x1016b6 5 ((0xffffeb35 : BitVec 32).signExtend 64)) 0x1016bb u12).Holds u12 u13 at e13
  have ag13 : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 80) 8, .rip] u12 u13 := by
      simpa only [callEffect, pushEffect_components, addr13] using e13.agrees
  have reg13 {r : BitVec 5} (h : r ≠ 4) : rd u13 r = rd u12 r := ag13.read (by simpa using h)
  have mem13 {k : Nat} (h : k+8 ≤ 80 ∨ 80+8 ≤ k) (hk : k ≤ 1104) :=
      slotKept (sp := stackPtr s) (w := 80) ag13 (by simp [Component.isMem]) h hk (by decide)

  have readTag := a1.trans (a2.trans a3)
  have writeDescriptor := a4.trans (a5.trans (a6.trans a7))
  have setArgs := a8.trans (a9.trans (a10.trans (a11.trans a12)))
  refine ⟨_, u13, readTag.trans (writeDescriptor.trans (setArgs.trans a13)), T13, e13.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (show stackPtr u13 = pushAddr u12 from e13.writes.1).trans addr13
  · change rd u13 7 = _
    exact by simp (disch := decide) only [reg13, reg12, reg11, reg10, reg9]; exact keyArg
  · change rd u13 1 = _
    exact by simp (disch := decide) only [reg13, reg12, reg11]; exact aadLengthArg
  · change rd u13 8 = _
    exact by simp (disch := decide) only [reg13, reg12]; exact descriptorArg
  · change rd u13 9 = _
    exact by simp (disch := decide) only [reg13]; exact tagArg
  · change wd u13 (stackPtr s - BitVec.ofNat 64 72) = p.tag.extractLsb' 64 64
    simp (disch := decide) only [mem13, mem12, mem11, mem10, mem9, mem8]
    exact tagSlot
  · exact addr13 ▸ (show wd u13 (pushAddr u12) = 0x1016bb from e13.writes.2)
  · change wd u13 (stackPtr s - BitVec.ofNat 64 56) = p.buf
    simp (disch := decide) only [mem13, mem12, mem11, mem10, mem9, mem8, mem7, mem6, mem5]
    exact srcSlot
  · change wd u13 (stackPtr s - BitVec.ofNat 64 48) = p.buf
    simp (disch := decide) only [mem13, mem12, mem11, mem10, mem9, mem8, mem7, mem6]
    exact dstSlot
  · change wd u13 (stackPtr s - BitVec.ofNat 64 40) = p.n
    simp (disch := decide) only [mem13, mem12, mem11, mem10, mem9, mem8, mem7]
    exact lengthSlot
  · intro i
    let k := 32-8*i.val
    have ki : i.val < 4 := i.isLt
    have kb : k ≤ 32 := Nat.sub_le _ _
    have addr : stackPtr s - 32 + BitVec.ofNat 64 (8*i.val) = stackPtr s - BitVec.ofNat 64 k :=
      sub_add_ofNat (stackPtr s) (a := 32) (b := 8*i.val) (by omega)
    have h := start.keyWords i
    rw [addr] at h ⊢
    change wd u13 (stackPtr s - BitVec.ofNat 64 k) = _
    have sep (w : Nat) (hw : 40 ≤ w) : k+8 ≤ w ∨ w+8 ≤ k :=
      Or.inl (Nat.le_trans (Nat.add_le_add_right kb 8) hw)
    have bound : k ≤ 1104 := Nat.le_trans kb (by decide)
    simp (disch := first | exact bound | exact sep _ (by decide)) only [mem13, mem12, mem11, mem10, mem9, mem8, mem7, mem6, mem5, mem4, mem3, mem2, mem1]
    exact h
end ChaCha20Poly1305.Proofs.DecryptInPlace
