import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Generate.LIR.Fn105f30
import K256.Proofs.Generate.Memory
import K256.Proofs.Generate.SigningKey
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Generate

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters

structure CopyReady (initial : RamState) (random : ByteArray) (args : Vector Value Reg.count)
    (mem : Ram) (d : Nat) (point : Curve.Point) : Prop where
  scalar : K256.Spec.Secp256k1.randomSecret random = some d
  publicKey : Keys.publicKey Secp256k1.domain (Encoding.natToOctets 32 d) = some point
  limbs : WordsAt mem (initial.regValue .rsp - 680) 64
    (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2 ^ (64 * i.val)))
  affine : Sec1.Parser.PublicKeyAt mem (initial.regValue .rsp - 544) point
  rsp : args[4] = ⟨64, initial.regValue .rsp - 680⟩
  df : args[22] = ⟨1, 0⟩
  key : memLoad mem (initial.regValue .rsp - 648) 64 = initial.regValue .rsp - 192
  dst : memLoad mem (initial.regValue .rsp - 336) 64 = initial.regValue .rdi
  r12 : memLoad mem (initial.regValue .rsp - 328) 64 = initial.regValue .r12
  r13 : memLoad mem (initial.regValue .rsp - 320) 64 = initial.regValue .r13
  r14 : memLoad mem (initial.regValue .rsp - 312) 64 = initial.regValue .rsp - 192
  r15 : memLoad mem (initial.regValue .rsp - 304) 64 = initial.regValue .r15
  rbp : memLoad mem (initial.regValue .rsp - 296) 64 = initial.regValue .rbp
  resume : memLoad mem (initial.regValue .rsp - 288) 64 = 0x102539
  savedRbx : memLoad mem (initial.regValue .rsp - 16) 64 = initial.regValue .rbx
  savedR14 : memLoad mem (initial.regValue .rsp - 8) 64 = initial.regValue .r14
  ret : memLoad mem (initial.regValue .rsp) 64 = (returnBoundary initial).rip
  writes : RamWriteFrame initial.external mem [Stack.region initial signingKeyGenerateFromRng.minStackBytes]

private theorem copyBlock {code : CodeMap} {args : Vector Value Reg.count}
    {mem m1 m2 m3 m4 final : Ram} {sp dst : BitVec 64}
    (hsp : args[4].get 64 = sp) (hdf : args[22].get 1 = 0)
    (hm1 : memStore mem (sp + 104) (memLoad mem sp 64) = m1)
    (hm2 : memStore m1 (sp + 112) (memLoad mem (sp + 8) 64) = m2)
    (hm3 : memStore m2 (sp + 120) (memLoad m2 (sp + 16) 64) = m3)
    (hm4 : memStore m3 (sp + 128) (memLoad m3 (sp + 24) 64) = m4)
    (hdst : memLoad m4 (sp + 32) 64 = dst)
    (hfinal : memCopy m4 dst (sp + 104) 120 = final)
    (hl0 : LoadOk mem sp 8) (hl8 : LoadOk mem (sp + 8) 8)
    (hl16 : LoadOk m2 (sp + 16) 8) (hl24 : LoadOk m3 (sp + 24) 8)
    (hl32 : LoadOk m4 (sp + 32) 8)
    (hs1 : StoreOk code mem (sp + 104) 8 0x1060d0 5)
    (hs2 : StoreOk code m1 (sp + 112) 8 0x1060d5 5)
    (hs3 : StoreOk code m2 (sp + 120) 8 0x1060df 5)
    (hs4 : StoreOk code m3 (sp + 128) 8 0x1060e9 8)
    (hcopy : RepMovsOk code m4 0 (sp + 104) dst 15 8 0x106103 3)
    (hpop : ∀ j ∈ [344, 352, 360, 368, 376, 384, 392],
      LoadOk final (sp + BitVec.ofNat 64 j) 8)
    (hret : memLoad final (sp + 392) 64 = 0x102539) :
    ∃ out, LIR.program.step (dialect code)
      ⟨⟨.l1060c7, args, mem⟩, [⟨.l102539, #v[], rfl, some ⟨64, 0x102539⟩⟩]⟩ =
      .next ⟨⟨.l102539, out, final⟩, []⟩ ∧
      out[3] = ⟨64, memLoad final (sp + 344) 64⟩ ∧
      out[4] = ⟨64, sp + 400⟩ ∧
      out[5] = ⟨64, memLoad final (sp + 384) 64⟩ ∧
      out[12] = ⟨64, memLoad final (sp + 352) 64⟩ ∧
      out[13] = ⟨64, memLoad final (sp + 360) 64⟩ ∧
      out[14] = ⟨64, memLoad final (sp + 368) 64⟩ ∧
      out[15] = ⟨64, memLoad final (sp + 376) 64⟩ ∧
      out[22] = args[22] := by
  have p344 : LoadOk final (sp + 344) 8 := hpop 344 (by decide)
  have p352 : LoadOk final (sp + 352) 8 := hpop 352 (by decide)
  have p360 : LoadOk final (sp + 360) 8 := hpop 360 (by decide)
  have p368 : LoadOk final (sp + 368) 8 := hpop 368 (by decide)
  have p376 : LoadOk final (sp + 376) 8 := hpop 376 (by decide)
  have p384 : LoadOk final (sp + 384) 8 := hpop 384 (by decide)
  have p392 : LoadOk final (sp + 392) 8 := hpop 392 (by decide)
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [hsp, hdf, hm1, hm2, hm3, hm4, hdst, hfinal]
    simp (config := { bitVecOfNat := false }) only
      [hl0, hl8, hl16, hl24, hl32, hs1, hs2, hs3, hs4,
       hcopy, false_or, p344, p352, p360, p368, p376, p384, p392, hret, and_true,
       BitVec.reduceToNat, Nat.reducePow, Nat.reduceLT, ↓reduceIte]
    rfl
  case post =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem copiedLoad (mem : Ram) (dst src : BitVec 64)
    {len off width : Nat} (hlen : len ≤ 2 ^ 64)
    (hin : off + width / 8 ≤ len) :
    memLoad (memCopy mem dst src len) (dst + BitVec.ofNat 64 off) width =
      memLoad mem (src + BitVec.ofNat 64 off) width := by
  apply memLoad_congr
  intro i hi
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, memByte, PhysicalMemory.read]
  rw [Sec1.Wrapper.Copy.memCopy_getElem?_self _ _ _ _ hlen _ (by omega), Option.getD_some]
  rfl

theorem copySigningKey {initial : RamState} {random : ByteArray} {args : Vector Value Reg.count}
    {mem : Ram} {d : Nat} {point : Curve.Point}
    (call : ValidCall signingKeyGenerateFromRng initial [random])
    (ready : CopyReady initial random args mem d point) :
    ∃ out final, Run.Reaches
      ⟨⟨.l1060c7, args, mem⟩, [⟨.l102539, #v[], rfl, some ⟨64, 0x102539⟩⟩]⟩
      ⟨⟨.l102539, out, final⟩, []⟩ ∧ KeyReady initial random out final d point := by
  let sp := initial.regValue .rsp - 680
  let dst := sp + 488
  let regions := [Stack.region initial signingKeyGenerateFromRng.minStackBytes]
  let m1 := memStore mem (sp + 104) (memLoad mem sp 64)
  let m2 := memStore m1 (sp + 112) (memLoad mem (sp + 8) 64)
  let m3 := memStore m2 (sp + 120) (memLoad m2 (sp + 16) 64)
  let m4 := memStore m3 (sp + 128) (memLoad m3 (sp + 24) 64)
  let final := memCopy m4 dst (sp + 104) 120
  have addr (j : Nat) (hj : j ≤ 680) :
      sp + BitVec.ofNat 64 j = stackPtr initial - BitVec.ofNat 64 (680 - j) := by
    change initial.regValue .rsp - 680 + BitVec.ofNat 64 j =
      initial.regValue .rsp - BitVec.ofNat 64 (680 - j)
    rw [← BitVec.ofNat_sub_ofNat_of_le 680 j (by omega) hj]
    bv_omega
  have inside {j len : Nat} (hj : j ≤ 680) (hl : j + len ≤ 688) :
      InRegions regions (sp + BitVec.ofNat 64 j) len := by
    rw [addr j hj]
    exact ⟨_, List.mem_cons_self, stackRange call (by omega) (by omega)⟩
  have frame1 : RamWriteFrame initial.external m1 regions :=
    ready.writes.memStore _ (inside (j := 104) (by decide) (by decide))
  have frame2 : RamWriteFrame initial.external m2 regions :=
    frame1.memStore _ (inside (j := 112) (by decide) (by decide))
  have frame3 : RamWriteFrame initial.external m3 regions :=
    frame2.memStore _ (inside (j := 120) (by decide) (by decide))
  have frame4 : RamWriteFrame initial.external m4 regions :=
    frame3.memStore _ (inside (j := 128) (by decide) (by decide))
  have frameFinal : RamWriteFrame initial.external final regions :=
    frame4.memStore _ (inside (j := 488) (by decide) (by decide))
  have writable {m : Ram} (frame : RamWriteFrame initial.external m regions)
      {j len : Nat} (hj : j ≤ 680) (hl : j + len ≤ 688) (hp : 0 < len) :
      Writable Extracted.programImage m (sp + BitVec.ofNat 64 j) len := by
    rw [addr j hj]
    exact (stackWritable call (by omega) (by omega) hp).of_frame frame
  have load {m : Ram} (frame : RamWriteFrame initial.external m regions)
      (j : Nat) (hj : j ≤ 680) :
      LoadOk m (sp + BitVec.ofNat 64 j) 8 :=
    let r := (writable frame hj (by omega) (by decide : 0 < 8)).readable
    ⟨r.low, r.present⟩
  have pos {j len : Nat} (hj : j ≤ 680) (hl : j + len ≤ 688) :
      (sp + BitVec.ofNat 64 j).toNat = (stackPtr initial).toNat - 680 + j ∧
      (sp + BitVec.ofNat 64 j).toNat + len ≤ 2 ^ 64 := by
    rw [addr j hj, stackOffset call (by omega)]
    have room : 10584 ≤ (stackPtr initial).toNat := call.stackAvailable.2.2.1
    have low := (stackWritable call (off := 0) (len := 8) (by decide) (by decide) (by decide)).readable.low
    rw [stackOffset call (off := 0) (by decide), Nat.sub_zero] at low
    omega
  have apart {j k n len : Nat} (hj : j ≤ 680) (hk : k ≤ 680)
      (hn : j + n ≤ 688) (hl : k + len ≤ 688)
      (sep : j + n ≤ k ∨ k + len ≤ j) :
      RangeApart (sp + BitVec.ofNat 64 j) n (sp + BitVec.ofNat 64 k) len := by
    obtain ⟨jNat, jLow⟩ := pos hj hn
    obtain ⟨kNat, kLow⟩ := pos hk hl
    apply RangeApart.of_toNat jLow kLow
    rw [jNat, kNat]
    omega
  have loadStore {m : Ram} {j k width : Nat} {v : BitVec 64}
      (hj : j ≤ 680) (hk : k ≤ 680) (hb : j + 8 ≤ 688) (hw : k + width / 8 ≤ 688)
      (sep : j + 8 ≤ k ∨ k + width / 8 ≤ j) :
      memLoad (memStore m (sp + BitVec.ofNat 64 j) v) (sp + BitVec.ofNat 64 k) width =
        memLoad m (sp + BitVec.ofNat 64 k) width :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (apart hj hk hb hw sep)
  have stagePreserves {j width : Nat} (hj : j ≤ 680) (hw : j + width / 8 ≤ 688)
      (sep : 136 ≤ j ∨ j + width / 8 ≤ 104) :
      memLoad m4 (sp + BitVec.ofNat 64 j) width = memLoad mem (sp + BitVec.ofNat 64 j) width := by
    dsimp only [m4, m3, m2, m1]
    exact (loadStore (j := 128) (by decide) hj (by decide) hw (by omega)).trans
      ((loadStore (j := 120) (by decide) hj (by decide) hw (by omega)).trans
        ((loadStore (j := 112) (by decide) hj (by decide) hw (by omega)).trans
          (loadStore (j := 104) (by decide) hj (by decide) hw (by omega))))
  have copyPreserves {j width : Nat} (hj : j ≤ 680) (hw : j + width / 8 ≤ 688)
      (sep : 608 ≤ j ∨ j + width / 8 ≤ 488) :
      memLoad final (sp + BitVec.ofNat 64 j) width = memLoad m4 (sp + BitVec.ofNat 64 j) width :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (j := 488) (by decide) hj (by decide) hw (by omega))
  have finalLoad {j width : Nat} (hj : j ≤ 680) (hw : j + width / 8 ≤ 688)
      (sepStage : 136 ≤ j ∨ j + width / 8 ≤ 104)
      (sepCopy : 608 ≤ j ∨ j + width / 8 ≤ 488) :
      memLoad final (sp + BitVec.ofNat 64 j) width = memLoad mem (sp + BitVec.ofNat 64 j) width :=
    (copyPreserves hj hw sepCopy).trans (stagePreserves hj hw sepStage)
  have code := fun x hx => Common.fnCode_subset_programImage x (LIR.code_l1060c7 x hx)
  have g1 : StoreOk Extracted.programImage mem (sp + 104) 8 0x1060d0 5 :=
    ParseSignature.storeOk_of_codeRange (off := 9) (writable ready.writes (by decide) (by decide) (by decide))
      code (by decide +kernel)
  have g2 : StoreOk Extracted.programImage m1 (sp + 112) 8 0x1060d5 5 :=
    ParseSignature.storeOk_of_codeRange (off := 14) (writable frame1 (by decide) (by decide) (by decide))
      code (by decide +kernel)
  have g3 : StoreOk Extracted.programImage m2 (sp + 120) 8 0x1060df 5 :=
    ParseSignature.storeOk_of_codeRange (off := 24) (writable frame2 (by decide) (by decide) (by decide))
      code (by decide +kernel)
  have g4 : StoreOk Extracted.programImage m3 (sp + 128) 8 0x1060e9 8 :=
    ParseSignature.storeOk_of_codeRange (off := 34) (writable frame3 (by decide) (by decide) (by decide))
      code (by decide +kernel)
  have copyGuard : RepMovsOk Extracted.programImage m4 0 (sp + 104) dst 15 8 0x106103 3 := by
    have source := (writable frame4 (j := 104) (len := 120) (by decide) (by decide) (by decide)).readable
    have into := writable frame4 (j := 488) (len := 120) (by decide) (by decide) (by decide)
    refine ⟨rfl, source.low, into.readable.low, source.present, into.readable.present, ?_, into.tables, ?_,
      into.notCode⟩
    · have hsrc := (pos (j := 104) (len := 120) (by decide) (by decide)).1
      have hdst := (pos (j := 488) (len := 120) (by decide) (by decide)).1
      change (sp + BitVec.ofNat 64 104).toNat + 120 ≤
        (sp + BitVec.ofNat 64 488).toNat ∨ (sp + BitVec.ofNat 64 488).toNat + 120 ≤
        (sp + BitVec.ofNat 64 104).toNat
      rw [hsrc, hdst]
      exact Or.inl (by omega)
    · have hcode : ∀ x ∈ codeRange 0x106103 [0xF3, 0x48, 0xA5], x ∈ Extracted.programImage := by
        intro x hx
        exact code _ (codeRange_mem_of_drop (p := 0x1060c7) (all := LIR.bytes_l1060c7)
          60 (by decide +kernel) x hx)
      intro i hi j hj he
      exact into.notCode _ (hcode _ (mem_codeRange 0x106103 [0xF3, 0x48, 0xA5] j hj)) i hi he.symm
  have dest : memLoad m4 (sp + 32) 64 = dst := by
    rw [show memLoad m4 (sp + 32) 64 = memLoad mem (sp + BitVec.ofNat 64 32) 64 from
      stagePreserves (by decide) (by decide) (by decide), addr 32 (by decide)]
    exact ready.key.trans (addr 488 (by decide)).symm
  have pop (j : Nat) (hj : j ∈ [344, 352, 360, 368, 376, 384, 392]) :
      LoadOk final (sp + BitVec.ofNat 64 j) 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    exact load frameFinal j (by omega)
  have resume : memLoad final (sp + 392) 64 = 0x102539 := by
    rw [show memLoad final (sp + 392) 64 = memLoad mem (sp + BitVec.ofNat 64 392) 64 from
      finalLoad (by decide) (by decide) (by decide) (by decide), addr 392 (by decide)]
    exact ready.resume
  obtain ⟨out, step, r3, r4, r5, r12, r13, r14, r15, r22⟩ :=
    copyBlock (sp := sp) (mem := mem) (m1 := m1) (m2 := m2) (m3 := m3) (m4 := m4) (final := final)
      (congrArg (Value.get 64) ready.rsp) (congrArg (Value.get 1) ready.df)
      rfl rfl rfl rfl dest rfl (by simpa only [BitVec.add_zero] using load ready.writes 0 (by decide))
      (load ready.writes 8 (by decide)) (load frame2 16 (by decide)) (load frame3 24 (by decide))
      (load frame4 32 (by decide)) g1 g2 g3 g4 copyGuard pop resume
  refine ⟨out, final, Semantics.Reaches.single step, ?_⟩
  have saved {j : Nat} {val : BitVec 64} (hj : j ≤ 680)
      (safe : j + 8 ≤ 488 ∨ 608 ≤ j)
      (afterScratch : 136 ≤ j)
      (old : memLoad mem (initial.regValue .rsp - BitVec.ofNat 64 (680 - j)) 64 = val) :
      memLoad final (sp + BitVec.ofNat 64 j) 64 = val := by
    rw [finalLoad hj (by omega) (Or.inl afterScratch) (by omega), addr j hj]
    exact old
  have skip {m : Ram} {v : BitVec 64} (j k : Nat)
      (sep : 8 ≤ (BitVec.ofNat 64 k - BitVec.ofNat 64 j).toNat ∧
        8 ≤ (BitVec.ofNat 64 j - BitVec.ofNat 64 k).toNat) :
      memLoad (memStore m (sp + BitVec.ofNat 64 j) v) (sp + BitVec.ofNat 64 k) 64 =
        memLoad m (sp + BitVec.ofNat 64 k) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl sep)
  have same (m : Ram) (j : Nat) (v : BitVec 64) :
      memLoad (memStore m (sp + BitVec.ofNat 64 j) v) (sp + BitVec.ofNat 64 j) 64 = v :=
    memLoad_memStore_same m _ v (by decide) (by decide)
  have word (i : Nat) (hi : i < 4) :
      memLoad m4 ((sp + 104) + BitVec.ofNat 64 (8 * i)) 64 =
        memLoad mem (sp + BitVec.ofNat 64 (8 * i)) 64 := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rw [BitVec.add_assoc]
    rcases h with rfl | rfl | rfl | rfl
    · exact (skip 128 104 (by decide)).trans ((skip 120 104 (by decide)).trans
        ((skip 112 104 (by decide)).trans ((same mem 104 _).trans
          (congrArg (fun a => memLoad mem a 64) (BitVec.add_zero sp).symm))))
    · exact (skip 128 112 (by decide)).trans ((skip 120 112 (by decide)).trans (same m1 112 _))
    · exact (skip 128 120 (by decide)).trans ((same m2 120 _).trans
        ((skip 112 16 (by decide)).trans (skip 104 16 (by decide))))
    · exact (same m3 128 _).trans ((skip 120 24 (by decide)).trans
        ((skip 112 24 (by decide)).trans (skip 104 24 (by decide))))
  refine ⟨ready.scalar, ready.publicKey, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frameFinal⟩
  · intro i hi
    change memLoad final ((initial.regValue .rsp - 192) + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [← show dst = initial.regValue .rsp - 192 from addr 488 (by decide),
      copiedLoad m4 dst (sp + 104) (by decide) (by omega), word i hi]
    exact ready.limbs i hi
  · obtain ⟨x, y, hp, ha⟩ := ready.affine
    refine ⟨x, y, hp, ha.of_copy ?_⟩
    intro off width hfit
    have srcAff : (initial.regValue .rsp - 544) + BitVec.ofNat 64 off =
        sp + BitVec.ofNat 64 (136 + off) := by
      rw [← show sp + BitVec.ofNat 64 136 = initial.regValue .rsp - 544 from addr 136 (by decide),
        BitVec.add_assoc, ← BitVec.ofNat_add]
    have dstBase : dst + BitVec.ofNat 64 32 = initial.regValue .rsp - 160 := by
      dsimp only [dst]
      rw [BitVec.add_assoc]
      exact addr 520 (by decide)
    have dstAff : (initial.regValue .rsp - 160) + BitVec.ofNat 64 off =
        dst + BitVec.ofNat 64 (32 + off) := by
      rw [← dstBase, BitVec.add_assoc, ← BitVec.ofNat_add]
    have srcOffset : (sp + 104) + BitVec.ofNat 64 (32 + off) =
        sp + BitVec.ofNat 64 (136 + off) := by
      rw [BitVec.add_assoc]
      change sp + (BitVec.ofNat 64 104 + BitVec.ofNat 64 (32 + off)) = _
      rw [← BitVec.ofNat_add, ← Nat.add_assoc]
    rw [srcAff, dstAff, copiedLoad m4 dst (sp + 104) (by decide) (by omega), srcOffset]
    exact stagePreserves (by omega) (by omega) (by omega)
  · exact r4.trans (congrArg (Value.mk 64) (addr 400 (by decide)))
  · exact r3.trans (congrArg (Value.mk 64) (saved (j := 344) (by decide) (by decide)
      (by decide) ready.dst))
  · exact r14.trans (congrArg (Value.mk 64) (saved (j := 368) (by decide) (by decide)
      (by decide) ready.r14))
  · rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact r5.trans (congrArg (Value.mk 64) (saved (j := 384) (by decide) (by decide)
        (by decide) ready.rbp))
    · exact r12.trans (congrArg (Value.mk 64) (saved (j := 352) (by decide) (by decide)
        (by decide) ready.r12))
    · exact r13.trans (congrArg (Value.mk 64) (saved (j := 360) (by decide) (by decide)
        (by decide) ready.r13))
    · exact r15.trans (congrArg (Value.mk 64) (saved (j := 376) (by decide) (by decide)
        (by decide) ready.r15))
    · exact r22.trans (ready.df.trans (Reg.read_df_iff.mpr call.directionFlagUnset).symm)
  · rw [← show sp + BitVec.ofNat 64 664 = initial.regValue .rsp - 16 from addr 664 (by decide)]
    exact saved (j := 664) (by decide) (by decide) (by decide) ready.savedRbx
  · rw [← show sp + BitVec.ofNat 64 672 = initial.regValue .rsp - 8 from addr 672 (by decide)]
    exact saved (j := 672) (by decide) (by decide) (by decide) ready.savedR14
  · have bottom : sp + BitVec.ofNat 64 680 = initial.regValue .rsp :=
      (addr 680 (by decide)).trans (BitVec.sub_zero _)
    rw [← bottom, finalLoad (by decide) (by decide) (by decide) (by decide), bottom]
    exact ready.ret

end K256.Proofs.Generate
