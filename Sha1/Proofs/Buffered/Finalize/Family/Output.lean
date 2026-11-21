import Sha1.Proofs.Buffered.Finalize.Family.Contracts
import Sha1.Proofs.Buffered.DigestFinish.Output

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST
open Sha1.Proofs.Compress.Machine

private abbrev textPC (offset : Nat) := Extracted.textAddress + BitVec.ofNat 64 offset

private def loadChanges : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .rip]

private structure Loads [Bindings] (b : ReturnBoundary) (s t : RamState) (pc : Nat) : Prop where
  steps : ∃ fuel, Advances b fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = textPC pc
  agrees : AgreesExcept loadChanges s t

private theorem Loads.rsp [Bindings] {b : ReturnBoundary} {s t : RamState} {pc : Nat}
    (h : Loads b s t pc) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by decide)

private theorem Loads.external [Bindings] {b : ReturnBoundary} {s t : RamState} {pc : Nat}
    (h : Loads b s t pc) : t.external = s.external :=
  h.agrees.external (by simp [loadChanges, Component.Covers])

private theorem Loads.next [Bindings] {b : ReturnBoundary} {s t u : RamState} {pc pc' : Nat}
    {r : BitVec 5} (h : Loads b s t pc) (ha : Advances b 1 t u) (hr : ReadyToStep u)
    (hip : u.RIP = textPC pc') (hf : AgreesExcept [.reg r, .rip] t u)
    (hreg : Component.reg r ∈ loadChanges) : Loads b s u pc' := by
  have hs : AgreesExcept loadChanges t u := hf.mono (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hreg
    · decide)
  obtain ⟨fuel, hsteps⟩ := h.steps
  exact ⟨⟨fuel + 1, hsteps.trans ha⟩, hr,
    h.code.of_external_eq (hs.external (by simp [loadChanges, Component.Covers])),
    hip, (h.agrees.trans hs).mono (by simp)⟩

private theorem Loads.word [Bindings] {b : ReturnBoundary} {s t : RamState} {pc pc' : Nat}
    {H : Vector (BitVec 32) 5} (h : Loads b s t pc)
    (storage : Storage .updateFinalizeCopy s) (state : StateBytes s H)
    (hOutside : ¬ InProgram b.rip) (k : Fin 5) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (haddr : ∀ x p, am.addr x p = stackPtr x + BitVec.ofNat 64 (8 + 4 * k.val))
    (hcode : CodeIn (codeRange (textPC pc) (0x8b :: am.modrm reg :: am.tail)) t)
    (hpc : textPC pc + BitVec.ofNat 64 (2 + am.tail.length) = textPC pc')
    (hlow : pc' < Extracted.textBytes.size) (hreg : Component.reg (gprNumber 0 0 reg) ∈ loadChanges) :
    ∃ u, Loads b s u pc' ∧ AgreesExcept [.reg (gprNumber 0 0 reg), .rip] t u ∧
      (Operand.reg (gprNumber 0 0 reg) : Operand 64).read u = H[k].setWidth 64 := by
  have hp : LoadPre (textPC pc)
      (fun x => am.addr x (textPC pc + BitVec.ofNat 64 (2 + am.tail.length))) 4 t := by
    refine ⟨h.rip, ?_⟩
    rw [haddr, h.rsp]
    exact (storage.stackWritable _ 4 (by change 8 + 4 * k.val + 4 ≤ 312; omega)).readable.of_external_eq
      h.external
  have hne := text_address_ne_return hOutside pc' hlow
  obtain ⟨u, ha, hr, he⟩ :=
    (DigestFinish.mov_r32_m32_noRex_effect_step (textPC pc) reg am hv hx hb).advances
      (boundary := b) h.ready hcode hp
      (show textPC pc + BitVec.ofNat 64 (2 + am.tail.length) ≠ b.rip from hpc.symm ▸ hne)
  refine ⟨u, h.next ha hr (he.rip.trans hpc) he.agrees hreg, he.agrees, ?_⟩
  have hw := he.writes
  change (Operand.reg (gprNumber 0 0 reg) : Operand 64).read u =
    ((Operand.mem (am.addr t (textPC pc + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read t).setWidth 64 at hw
  rw [hw, haddr, h.rsp, BitVec.ofNat_add, ← BitVec.add_assoc]
  change (memLoad t.external _ 32).setWidth 64 = _
  rw [h.external]
  exact congrArg (BitVec.setWidth 64) (Compress.stateBytes_words state k)

private theorem Loads.bswap [Bindings] {b : ReturnBoundary} {s t : RamState} {pc pc' : Nat}
    (h : Loads b s t pc) (hOutside : ¬ InProgram b.rip) (op : UInt8)
    (hop : op ∈ [0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf])
    (hcode : CodeIn (codeRange (textPC pc) [0x0f, op]) t)
    (hpc : textPC pc + 2#64 = textPC pc') (hlow : pc' < Extracted.textBytes.size)
    (hreg : Component.reg (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) ∈ loadChanges) :
    let r := gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)
    ∃ u, Loads b s u pc' ∧ AgreesExcept [.reg r, .rip] t u ∧
      (Operand.reg r : Operand 64).read u =
        (bswapSpec ((Operand.reg r : Operand 32).read t)).setWidth 64 := by
  have hne := text_address_ne_return hOutside pc' hlow
  obtain ⟨u, ha, hr, hi, hf, hw⟩ := DigestFinish.bswap_step (boundary := b) (textPC pc) op hop
    h.ready hcode h.rip (hpc.symm ▸ hne)
  exact ⟨u, h.next ha hr (hi.trans hpc) hf hreg, hf, hw⟩

private theorem Loads.pointer [Bindings] {b : ReturnBoundary} {s t : RamState}
    (h : Loads b s t 0x1f9e) (storage : Storage .updateFinalizeCopy s)
    (hOutside : ¬ InProgram b.rip) :
    ∃ u, Loads b s u 0x1fa6 ∧ AgreesExcept [.reg 8, .rip] t u ∧
      (Operand.reg 8 : Operand 64).read u = savedOutput s := by
  have hp : LoadPre (textPC 0x1f9e)
      (fun x => (AddrMode.sib 4 none 0 (.d32 0xc0)).addr x (textPC 0x1fa6)) 8 t := by
    refine ⟨h.rip, ?_⟩
    change MemReadable t (stackPtr t + 0xc0) 8
    rw [h.rsp]
    exact (storage.stackWritable 0xc0 8 (by decide)).readable.of_external_eq h.external
  obtain ⟨u, ha, hr, he⟩ :=
    (mov_r64_m64_effect_step (textPC 0x1f9e) 0x4c (by decide) 0
      (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)).advances
      h.ready (program_text_slice h.code 0x1f9e 8 (by decide +kernel)) hp
      (text_address_ne_return hOutside 0x1fa6 (by decide +kernel))
  refine ⟨u, h.next ha hr he.rip he.agrees (by decide), he.agrees, ?_⟩
  have hw := he.writes
  change (Operand.reg 8 : Operand 64).read u = savedOutput t at hw
  rw [hw]
  change memLoad t.external (stackPtr t + 0xc0) 64 = memLoad s.external (stackPtr s + 0xc0) 64
  rw [h.rsp, h.external]

private def outputReg (i : Fin 5) : BitVec 3 :=
  #v[0, 1, 2, 6, 7][i]

private theorem read32_of_read64 {s : RamState} {r : BitVec 5} {v : BitVec 32}
    (h : (Operand.reg r : Operand 64).read s = v.setWidth 64) :
    (Operand.reg r : Operand 32).read s = v := by
  change ((Operand.reg r : Operand 64).read s).setWidth 32 = v
  rw [h, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

private theorem load_words [Bindings] {b : ReturnBoundary} {s : RamState} {H : Vector (BitVec 32) 5}
    (hOutside : ¬ InProgram b.rip) (storage : Storage .updateFinalizeCopy s)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s)
    (rip : s.RIP = textPC 0x1f80) (state : StateBytes s H) :
    ∃ t, Loads b s t 0x1fa6 ∧ (Operand.reg 8 : Operand 64).read t = savedOutput s ∧
      ∀ i : Fin 5, (Operand.reg (gprNumber 0 0 (outputReg i)) : Operand 32).read t = bswapSpec H[i] := by
  have l0 : Loads b s s 0x1f80 :=
    ⟨⟨0, (advances_zero ..).mpr rfl⟩, ready, code, rip, AgreesExcept.refl ..⟩
  obtain ⟨_, l1, _, v1⟩ := l0.word (pc' := 0x1f84) storage state hOutside 0 0 (.sib 4 none 0 (.d8 8))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice l0.code 0x1f80 4 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l2, a2, v2⟩ := l1.word (pc' := 0x1f88) storage state hOutside 1 1 (.sib 4 none 0 (.d8 12))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice l1.code 0x1f84 4 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l3, a3, v3⟩ := l2.bswap (pc' := 0x1f8a) hOutside 0xc8 (by decide)
    (program_text_slice l2.code 0x1f88 2 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l4, a4, v4⟩ := l3.bswap (pc' := 0x1f8c) hOutside 0xc9 (by decide)
    (program_text_slice l3.code 0x1f8a 2 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l5, a5, v5⟩ := l4.word (pc' := 0x1f90) storage state hOutside 2 2 (.sib 4 none 0 (.d8 16))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice l4.code 0x1f8c 4 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l6, a6, v6⟩ := l5.bswap (pc' := 0x1f92) hOutside 0xca (by decide)
    (program_text_slice l5.code 0x1f90 2 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l7, a7, v7⟩ := l6.word (pc' := 0x1f96) storage state hOutside 3 6 (.sib 4 none 0 (.d8 20))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice l6.code 0x1f92 4 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l8, a8, v8⟩ := l7.bswap (pc' := 0x1f98) hOutside 0xce (by decide)
    (program_text_slice l7.code 0x1f96 2 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l9, a9, v9⟩ := l8.word (pc' := 0x1f9c) storage state hOutside 4 7 (.sib 4 none 0 (.d8 24))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice l8.code 0x1f98 4 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨_, l10, a10, v10⟩ := l9.bswap (pc' := 0x1f9e) hOutside 0xcf (by decide)
    (program_text_slice l9.code 0x1f9c 2 (by decide +kernel)) (by decide) (by decide +kernel) (by decide)
  obtain ⟨t, l11, a11, ptr⟩ := l10.pointer storage hOutside
  refine ⟨t, l11, ptr, ?_⟩
  intro ⟨i, hi⟩
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl
  · change (Operand.reg 0 : Operand 32).read t = bswapSpec H[0]
    erw [a11.read (by decide), a10.read (by decide), a9.read (by decide), a8.read (by decide),
      a7.read (by decide), a6.read (by decide), a5.read (by decide), a4.read (by decide),
      read32_of_read64 v3, a2.read (by decide), read32_of_read64 v1]
    rfl
  · change (Operand.reg 1 : Operand 32).read t = bswapSpec H[1]
    erw [a11.read (by decide), a10.read (by decide), a9.read (by decide), a8.read (by decide),
      a7.read (by decide), a6.read (by decide), a5.read (by decide),
      read32_of_read64 v4, a3.read (by decide), read32_of_read64 v2]
    rfl
  · change (Operand.reg 2 : Operand 32).read t = bswapSpec H[2]
    erw [a11.read (by decide), a10.read (by decide), a9.read (by decide), a8.read (by decide),
      a7.read (by decide), read32_of_read64 v6, read32_of_read64 v5]
    rfl
  · change (Operand.reg 6 : Operand 32).read t = bswapSpec H[3]
    erw [a11.read (by decide), a10.read (by decide), a9.read (by decide),
      read32_of_read64 v8, read32_of_read64 v7]
    rfl
  · change (Operand.reg 7 : Operand 32).read t = bswapSpec H[4]
    erw [a11.read (by decide), read32_of_read64 v10, read32_of_read64 v9]
    rfl

private structure Stores [Bindings] (b : ReturnBoundary) (out : BitVec 64)
    (H : Vector (BitVec 32) 5) (s t : RamState) (pc count : Nat) : Prop where
  steps : Advances b count s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = textPC pc
  agrees : AgreesExcept [.mem out 20, .rip] s t
  region : Common.StoreRegion Extracted.programImage t.external ⟨out.toNat, 20⟩
  written : ∀ i : Fin 5, i.val < count →
    memLoad t.external (out + BitVec.ofNat 64 (4 * i.val)) 32 = bswapSpec H[i]

private theorem Stores.word [Bindings] {b : ReturnBoundary} {s t : RamState} {pc pc' : Nat}
    {H : Vector (BitVec 32) 5} {out : BitVec 64} (i : Fin 5) (h : Stores b out H s t pc i.val)
    (ptr : (Operand.reg 8 : Operand 64).read s = out)
    (word : (Operand.reg (gprNumber 0 0 (outputReg i)) : Operand 32).read s = bswapSpec H[i])
    (hOutside : ¬ InProgram b.rip) (am : AddrMode) (hv : am.Valid)
    (hx : rexX (0x41 : UInt8).toBitVec = am.rexX) (hb : rexB (0x41 : UInt8).toBitVec = am.rexB)
    (haddr : ∀ x p, am.addr x p =
      (Operand.reg 8 : Operand 64).read x + BitVec.ofNat 64 (4 * i.val))
    (hcode : CodeIn (codeRange (textPC pc) (0x41 :: 0x89 :: am.modrm (outputReg i) :: am.tail)) t)
    (hin : ∀ j < 3 + am.tail.length, InProgram (textPC pc + BitVec.ofNat 64 j))
    (hpc : textPC pc + BitVec.ofNat 64 (3 + am.tail.length) = textPC pc')
    (hlow : pc' < Extracted.textBytes.size) :
    ∃ u, Stores b out H s u pc' (i.val + 1) := by
  have hptr : (Operand.reg 8 : Operand 64).read t = out :=
    (h.agrees.read (by simp)).trans ptr
  have ha : storeAddrAt (textPC pc) am (3 + am.tail.length) t = out + BitVec.ofNat 64 (4 * i.val) := by
    simp only [storeAddrAt, haddr, hptr]
  have hi : 4 * i.val + 4 ≤ 20 := by omega
  have hpre := DigestFinish.output_pre h.region h.rip (addr := storeAddrAt (textPC pc) am
    (3 + am.tail.length)) ha hi hin
  have hne := text_address_ne_return hOutside pc' hlow
  obtain ⟨u, hstep, hready, he⟩ :=
    (Common.Instructions.MovStore.mov_m32_r32_effect_step (textPC pc) 0x41 (by decide)
      (outputReg i) am hv hx hb).advances (boundary := b) h.ready hcode hpre
      (show textPC pc + BitVec.ofNat 64 (3 + am.tail.length) ≠ b.rip from hpc.symm ▸ hne)
  have hc : (movM32R32Effect (textPC pc) (gprNumber 0 0 (outputReg i)) am t).components =
      [.mem (out + BitVec.ofNat 64 (4 * i.val)) 4, .rip] := by
    simp only [movM32R32Effect, storeEffect_components, ha]
  have hf : AgreesExcept (movM32R32Effect (textPC pc) (gprNumber 0 0 (outputReg i)) am t).components t u :=
    he.agrees
  rw [hc] at hf
  have hwide : AgreesExcept [.mem out 20, .rip] t u := by
    apply hf.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · contradiction
      · simp
    · intro x c hc hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcover
        refine ⟨.mem out 20, by simp, 4 * i.val + j, by omega, ?_⟩
        rw [BitVec.ofNat_add, BitVec.add_assoc]
      · exact False.elim hcover
  refine ⟨u, h.steps.trans hstep, hready,
    he.codeIn (DigestFinish.output_avoid h.region hc hi (fun _ hx ↦ hx)) h.code,
    he.rip.trans hpc, (h.agrees.trans hwide).mono (by simp),
    DigestFinish.output_region_of_holds h.region he, ?_⟩
  intro j hj
  by_cases eq : j = i
  · subst j
    have hw := he.writes
    change memLoad u.external (storeAddrAt (textPC pc) am (3 + am.tail.length) t) 32 =
      (Operand.reg (gprNumber 0 0 (outputReg i)) : Operand 32).read t at hw
    rw [ha] at hw
    exact hw.trans ((h.agrees.read (by simp)).trans word)
  · have earlier : j.val < i.val := by
      have hv : j.val ≠ i.val := fun e ↦ eq (Fin.ext e)
      omega
    exact (DigestFinish.store_keeps he hc h.region.bounded (by omega) hi (Or.inl (by omega))).trans
      (h.written j earlier)

theorem write_output [Bindings] {b : ReturnBoundary} {H : Vector (BitVec 32) 5} {s : RamState}
    (hOutside : ¬ InProgram b.rip) (storage : Storage .updateFinalizeCopy s)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s)
    (rip : s.RIP = 0x101f80) (state : StateBytes s H)
    (bounded : (Kind.resultRegion .updateFinalizeCopy s).Bounded)
    (allocated : (Kind.resultRegion .updateFinalizeCopy s).Allocated s.external)
    (disjoint : (Kind.resultRegion .updateFinalizeCopy s).Disjoint (Kind.stackRegion .updateFinalizeCopy s))
    (avoids : (Kind.resultRegion .updateFinalizeCopy s).Avoids
      (fun a ↦ InProgram a ∨ InPageTables a)) :
    ∃ t, Run b s t ∧ t.RIP = 0x101fb9 ∧ (Kind.resultRegion .updateFinalizeCopy s).HasBytes
      t.external ⟨(SHA1.toDigest H).bytes.toArray⟩ := by
  obtain ⟨u, loads, ptr, words⟩ := load_words hOutside storage ready code rip state
  let out := savedOutput s
  have source : Common.StoreRegion Extracted.programImage u.external ⟨out.toNat, 20⟩ :=
    ⟨bounded, by rw [loads.external]; exact allocated, avoids⟩
  have h0 : Stores b out H u u 0x1fa6 0 :=
    ⟨(advances_zero ..).mpr rfl, loads.ready, loads.code, loads.rip,
      AgreesExcept.refl .., source, fun _ h ↦ (Nat.not_lt_zero _ h).elim⟩
  obtain ⟨_, h1⟩ := h0.word (pc' := 0x1fa9) 0 ptr (words 0) hOutside (.base 8 .none)
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice h0.code 0x1fa6 3 (by decide +kernel))
    (program_text_range 0x1fa6 3 (by decide +kernel)) (by decide) (by decide +kernel)
  obtain ⟨_, h2⟩ := h1.word (pc' := 0x1fad) 1 ptr (words 1) hOutside (.base 8 (.d8 4))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice h1.code 0x1fa9 4 (by decide +kernel))
    (program_text_range 0x1fa9 4 (by decide +kernel)) (by decide) (by decide +kernel)
  obtain ⟨_, h3⟩ := h2.word (pc' := 0x1fb1) 2 ptr (words 2) hOutside (.base 8 (.d8 8))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice h2.code 0x1fad 4 (by decide +kernel))
    (program_text_range 0x1fad 4 (by decide +kernel)) (by decide) (by decide +kernel)
  obtain ⟨_, h4⟩ := h3.word (pc' := 0x1fb5) 3 ptr (words 3) hOutside (.base 8 (.d8 12))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice h3.code 0x1fb1 4 (by decide +kernel))
    (program_text_range 0x1fb1 4 (by decide +kernel)) (by decide) (by decide +kernel)
  obtain ⟨t, h5⟩ := h4.word (pc' := 0x1fb9) 4 ptr (words 4) hOutside (.base 8 (.d8 16))
    (by decide) (by decide) (by decide) (by intros; rfl)
    (program_text_slice h4.code 0x1fb5 4 (by decide +kernel))
    (program_text_range 0x1fb5 4 (by decide +kernel)) (by decide) (by decide +kernel)
  have rsp : stackPtr t = stackPtr s :=
    (h5.agrees.read (n := 64) (r := 4) (by simp)).trans loads.rsp
  have hin := DigestFinish.output_inside h5.region 0 20 (by decide)
  change Sha1.Proofs.Refine.InRegion ⟨out.toNat, 20⟩ (out + 0#64) 20 at hin
  rw [BitVec.add_zero] at hin
  have contains (i : Nat) (hi : i < 20) :
      (Kind.resultRegion .updateFinalizeCopy s).Contains (out + BitVec.ofNat 64 i).toNat :=
    Common.StoreRegion.contains_byte hin hi
  have saved : savedOutput t = savedOutput s := by
    change memLoad t.external (stackPtr t + 0xc0) 64 = memLoad s.external (stackPtr s + 0xc0) 64
    rw [rsp, ← loads.external]
    apply memLoad_congr
    intro i hi
    unfold memByte
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    apply h5.agrees.byte
    intro c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hcover
      have ho := heq.symm ▸ contains j hj
      exact disjoint _ ho (storage.stackCover (offset := 0xc0) (len := 8) (by decide) ⟨i, hi, rfl⟩)
    · exact hcover
  have agrees := (loads.agrees.trans h5.agrees).mono (cs' := Kind.changes .updateFinalizeCopy s) (by
    intro c hc
    simp only [loadChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
      simp [Kind.changes, Kind.workRegisters, Kind.localChanges, out, savedOutput])
  obtain ⟨fuel, hsteps⟩ := loads.steps
  refine ⟨t, ⟨⟨_, hsteps.trans h5.steps⟩, h5.ready, h5.code, rsp, saved, agrees⟩, h5.rip, ?_⟩
  change (⟨out.toNat, 20⟩ : MemoryRegion).HasBytes t.external _
  rw [← DigestFinish.stateBytes_bswap_eq_toDigest]
  refine Compress.stateBytes_of_words (H := H.map bswapSpec) (fun i ↦ ?_) (fun i hi ↦ ?_)
  · change memLoad t.external (out + BitVec.ofNat 64 (4 * i.val)) 32 = (H.map bswapSpec)[i.val]
    rw [Vector.getElem_map]
    exact h5.written i i.isLt
  · exact Option.isSome_iff_exists.mpr (h5.region.allocated _ (contains i hi))

end Sha1.Proofs.Buffered.Finalize.Family
