import K256.Proofs.Generate.Wrapper.Memory
import K256.Proofs.Generate.Serialize.Transfer
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Common.WordCopy
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Sec1.Wrapper.Calls

namespace K256.Proofs.Generate.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters K256.Proofs.Generate.LIR

private def copyWord (src dst : BitVec 64) (before after : Ram) (off : BitVec 64) : Ram :=
  memStore after (dst + off) (memLoad before (src + off) 64)

private def pointArgs (args : Vector Value Reg.count) (mem : Ram) (p : BitVec 64) : Vector Value Reg.count :=
  (((((args.set 0 ⟨64, memLoad mem p 64⟩).set 1 ⟨64, memLoad mem (p + 8) 64⟩).set
    2 ⟨64, 0⟩).set 4 ⟨64, p - 8⟩).set 6 ⟨64, p + 120⟩).set 7 ⟨64, p⟩

private theorem pointBlock {code : CodeMap} {args : Vector Value Reg.count} {mem : Ram}
    {p dst : BitVec 64} (rsp : args[4].get 64 = p) (rbx : args[3].get 64 = dst) :
    let m1 := copyWord p dst mem mem 24
    let m2 := copyWord p dst mem m1 16
    let m3 := copyWord p dst mem m2 8
    let m4 := memStore m3 dst (memLoad mem p 64)
    LoadOk mem (p + 24) 8 →
    LoadOk m1 (p + 16) 8 →
    LoadOk m2 p 8 →
    LoadOk m2 (p + 8) 8 →
    memLoad m1 (p + 16) 64 = memLoad mem (p + 16) 64 →
    memLoad m2 p 64 = memLoad mem p 64 →
    memLoad m2 (p + 8) 64 = memLoad mem (p + 8) 64 →
    StoreOk code mem (dst + 24) 8 0x102549 4 →
    StoreOk code m1 (dst + 16) 8 0x102552 4 →
    StoreOk code m2 (dst + 8) 8 0x10255f 4 →
    StoreOk code m3 dst 8 0x102563 3 →
    StoreOk code m4 (p - 8) 8 0x102570 5 →
    program.runBlock (dialect code) ⟨.l102544, args, mem⟩ =
      .call ⟨.l1215e0, pointArgs args mem p, memStore m4 (p - 8) (0x102575 : BitVec 64)⟩
        (Generator.callFrame .l102575 0x102575) := by
  dsimp only
  intro l24 l16 l0 l8 e16 e0 e8 s24 s16 s8 s0 push
  simp only [copyWord] at l16 l0 l8 e16 e0 e8 s16 s8 s0 push
  cfg_eval
  simp only [rsp, rbx, l24, l16, l0, l8, e16, e0, e8, s24, s16, s8, s0, push,
    copyWord, ↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [pointArgs, Vector.getElem_set] <;> rfl

variable {s : RamState} {random : ByteArray} {args : Vector Value Reg.count} {mem : Ram}

private theorem outsideOutput (call : ValidCall signingKeyGenerateFromRng s [random])
    {a : BitVec 64} {n : Nat}
    (h : InRegion (Stack.region s signingKeyGenerateFromRng.minStackBytes) a n) :
    Outside [⟨(s.regValue .rdi).toNat, 32⟩] a n := by
  have room := call.stackAvailable.2.2.1
  have sep := output_stack_apart call
  obtain ⟨above, below, low⟩ := h
  change (s.regValue .rsp).toNat - 10584 ≤ a.toNat at above
  change a.toNat + n ≤ (s.regValue .rsp).toNat - 10584 +
    ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10584)) at below
  refine ⟨low, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change a.toNat + n ≤ (s.regValue .rdi).toNat ∨ (s.regValue .rdi).toNat + 32 ≤ a.toNat
  omega

private theorem copyWords (src dst : BitVec 64) (before after : Ram)
    (stores : after = memStore (copyWord src dst before
      (copyWord src dst before (copyWord src dst before before 24) 16) 8) dst (memLoad before src 64)) :
    ∀ i < 4, memLoad after (wordAddr dst 64 i) 64 = memLoad before (wordAddr src 64 i) 64 := by
  intro i hi
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rw [stores]
  rcases casesI with rfl | rfl | rfl | rfl
  · have zero (p : BitVec 64) : wordAddr p 64 0 = p := by
      change p + 0 = p
      bv_omega
    rw [zero dst, zero src, memLoad_memStore_same _ _ _ (by decide) (by decide)]
  · change memLoad (memStore (memStore _ (dst + 8) (memLoad before (src + 8) 64))
      dst _) (dst + 8) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (addr_self dst) rfl (by decide)),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    rfl
  · change memLoad (memStore (memStore (memStore _ (dst + 16) (memLoad before (src + 16) 64))
      (dst + 8) _) dst _) (dst + 16) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (addr_self dst) rfl (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := dst) rfl rfl (by decide)),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    rfl
  · change memLoad (memStore (memStore (memStore (memStore _ (dst + 24)
      (memLoad before (src + 24) 64)) (dst + 16) _) (dst + 8) _) dst _) (dst + 24) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (addr_self dst) rfl (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := dst) rfl rfl (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := dst) rfl rfl (by decide)),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    rfl

theorem point {d : Nat} {pt : Curve.Point} (call : ValidCall signingKeyGenerateFromRng s [random])
    (f : CallerFrame s args mem) (dst : args[3] = ⟨64, s.regValue .rdi⟩) (width : args[14].width = 64)
    (affine : Sec1.Parser.PublicKeyAt mem (s.regValue .rsp - 160) pt)
    (scalar : atBytes (s.regValue .rsp - 280) 32 mem (Encoding.natToOctets 32 d)) :
    ∃ a m, Segment .l102544 args mem .l102575 a m ∧ CallerFrame s a m ∧
      a[3] = ⟨64, s.regValue .rdi⟩ ∧ memLoad m (s.regValue .rsp - 280) 8 = 4 ∧
      atBytes (s.regValue .rdi) 32 m (Encoding.natToOctets 32 d) ∧
      atBytes (s.regValue .rsp - 280) 65 m (Points.encodePoint Secp256k1.domain false pt) := by
  let sp := s.regValue .rsp
  let p := sp - 280
  let dest := s.regValue .rdi
  let src := sp - 160
  let entry := sp - 288
  let lo := sp - 736
  let m1 := copyWord p dest mem mem 24
  let m2 := copyWord p dest mem m1 16
  let m3 := copyWord p dest mem m2 8
  let m4 := memStore m3 dest (memLoad mem p 64)
  let child := memStore m4 entry (0x102575 : BitVec 64)
  let a := pointArgs args mem p
  have entryEq : p - 8 = entry := by dsimp only [p, entry]; bv_omega
  have srcEq : p + 120 = src := by dsimp only [p, src]; bv_omega
  have loEq : entry - 448 = lo := by dsimp only [entry, lo]; bv_omega
  have stackW {off len : Nat} (depth : off ≤ 10584) (fits : len ≤ off + 8) (pos : 0 < len) :=
    (stackWritable call depth fits pos).of_frame f.writes
  have destW : Writable Extracted.programImage mem dest 97 := (outputWritable call).of_frame f.writes
  have destLow := destW.readable.low
  have destWord {c : BitVec 64} (limit : c.toNat + 8 ≤ 32) :
      InRegions [⟨dest.toNat, 32⟩] (dest + c) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change dest.toNat ≤ (dest + c).toNat ∧ (dest + c).toNat + 8 ≤ dest.toNat + 32 ∧ _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega
  have f1 : RamWriteFrame mem m1 [⟨dest.toNat, 32⟩] :=
    (RamWriteFrame.refl _ _).memStore _ (destWord (c := 24) (by decide))
  have f2 : RamWriteFrame mem m2 [⟨dest.toNat, 32⟩] :=
    f1.memStore _ (destWord (c := 16) (by decide))
  have f3 : RamWriteFrame mem m3 [⟨dest.toNat, 32⟩] :=
    f2.memStore _ (destWord (c := 8) (by decide))
  have f4 : RamWriteFrame mem m4 [⟨dest.toNat, 32⟩] := by
    apply f3.memStore
    simpa only [show dest + (0 : BitVec 64) = dest by bv_omega] using destWord (c := 0) (by decide)
  have destWithin : RegionsWithin [⟨dest.toNat, 32⟩] (regions s).toList := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputRegion signingKeyGenerateFromRng s, List.mem_cons_self, Nat.le_refl _, by
      change dest.toNat + 32 ≤ dest.toNat + 97
      omega⟩
  have childFrame : RamWriteFrame s.external child (regions s).toList :=
    (f.writes.trans f4 destWithin).memStore _
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, stackRange (off := 288) call (by decide) (by decide)⟩
  have load {m : Ram} (fr : RamWriteFrame mem m [⟨dest.toNat, 32⟩])
      {c : BitVec 64} (limit : c.toNat + 8 ≤ 32) : LoadOk m (p + c) 8 :=
    LoadOk.of_offsets ((stackW (off := 280) (len := 32) (by decide) (by decide) (by decide)).readable.of_frame fr)
      rfl (addr_self p) (by simpa only [show c - (0 : BitVec 64) = c by bv_omega] using limit)
  have original {m : Ram} (fr : RamWriteFrame mem m [⟨dest.toNat, 32⟩])
      {off : Nat} (depth : off ≤ 10584) :
      memLoad m (sp - BitVec.ofNat 64 off) 64 = memLoad mem (sp - BitVec.ofNat 64 off) 64 :=
    fr.memLoad_eq (outsideOutput call (stackRange call depth (Nat.le_add_left 8 off)))
  have write {m : Ram} (fr : RamWriteFrame mem m [⟨dest.toNat, 32⟩])
      {c : BitVec 64} (limit : c.toNat + 8 ≤ 32) :
      Writable Extracted.programImage m (dest + c) 8 :=
    (destW.of_frame fr).of_offsets rfl (addr_self dest) (by
      rw [show c - (0 : BitVec 64) = c by bv_omega]
      omega)
  have includeBlock := fun x hx => Common.fnCode_subset_programImage x (code_l102544 x hx)
  have store {m : Ram} {addr : BitVec 64} {off len : Nat}
      (hw : Writable Extracted.programImage m addr 8) (fit : off + len ≤ bytes_l102544.length) :=
    ParseSignature.storeOk_of_codeRange hw includeBlock fit
  have e16 : p + 16 = sp - 264 := by dsimp only [p]; bv_omega
  have e8 : p + 8 = sp - 272 := by dsimp only [p]; bv_omega
  have read0 : LoadOk m2 p 8 := by
    simpa only [show p + (0 : BitVec 64) = p by bv_omega] using load f2 (c := 0) (by decide)
  have write0 : Writable Extracted.programImage m3 dest 8 := by
    simpa only [show dest + (0 : BitVec 64) = dest by bv_omega] using write f3 (c := 0) (by decide)
  have block : program.runBlock (dialect Extracted.programImage) ⟨.l102544, args, mem⟩ =
      .call ⟨.l1215e0, a, child⟩ (Generator.callFrame .l102575 0x102575) := by
    dsimp only [child, a]
    rw [← entryEq]
    apply pointBlock (by rw [f.rsp]; rfl) (by rw [dst]; rfl)
    · exact load (RamWriteFrame.refl _ _) (by decide)
    · exact load f1 (by decide)
    · exact read0
    · exact load f2 (by decide)
    · rw [e16]
      exact original f1 (off := 264) (by decide)
    · exact original f2 (off := 280) (by decide)
    · rw [e8]
      exact original f2 (off := 272) (by decide)
    · exact store (off := 5) (write (RamWriteFrame.refl _ _) (by decide)) (by decide)
    · exact store (off := 14) (write f1 (by decide)) (by decide)
    · exact store (off := 27) (write f2 (by decide)) (by decide)
    · exact store (off := 31) write0 (by decide)
    · rw [entryEq]
      exact store (off := 44) ((stackW (off := 288) (by decide) (by decide) (by decide)).of_frame f4)
        (by decide)
  have eqArgs (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22]) : a[i] = args[i] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases i with ⟨i, hi'⟩
    change a[i] = args[i]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [a, pointArgs, Vector.getElem_set] <;> rfl
  have childWidth (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : a[i].width = 64 := by
    rw [eqArgs i (List.mem_append_left [22] hi)]
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width dst
    · change args[5].width = 64
      exact congrArg Value.width (f.kept 5 (by decide))
    · change args[12].width = 64
      exact congrArg Value.width (f.kept 12 (by decide))
    · change args[13].width = 64
      exact congrArg Value.width (f.kept 13 (by decide))
    · exact width
    · change args[15].width = 64
      exact congrArg Value.width (f.kept 15 (by decide))
  have childDf := (eqArgs 22 (by decide)).trans
    ((f.kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset))
  have srcRead := ((stackWritable (off := 160) (len := 88) call
    (by decide) (by decide) (by decide)).of_frame childFrame).readable
  have pWrite := (stackWritable (off := 280) (len := 65) call
    (by decide) (by decide) (by decide)).of_frame childFrame
  have loWrite := (stackWritable (off := 736) (len := 456) call
    (by decide) (by decide) (by decide)).of_frame childFrame
  have ret : memLoad child entry 64 = 0x102575 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have room : 10584 ≤ sp.toNat := call.stackAvailable.2.2.1
  have align : sp.toNat % 16 = 8 := call.stackAvailable.2.2.2
  have entryNat : entry.toNat = sp.toNat - 288 := stackOffset (off := 288) call (by decide)
  have pNat : p.toNat = sp.toNat - 280 := stackOffset (off := 280) call (by decide)
  have srcNat : src.toNat = sp.toNat - 160 := stackOffset (off := 160) call (by decide)
  have loNat : lo.toNat = sp.toNat - 736 := stackOffset (off := 736) call (by decide)
  have retSrc : RangeApart entry 8 src 88 :=
    RangeApart.of_offsets (addr_sub sp 288) (addr_sub sp 160) (by decide)
  have childPoint : Sec1.Parser.PublicKeyAt child src pt := by
    obtain ⟨x,y,eq,xy⟩ := affine
    refine ⟨x,y,eq,xy.of_copy ?_⟩
    intro off w fit
    have low := srcRead.low
    have offNat : (src + BitVec.ofNat 64 off).toNat = src.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have inside : InRegion (Stack.region s signingKeyGenerateFromRng.minStackBytes)
        (src + BitVec.ofNat 64 off) (w / 8) := by
      change sp.toNat - 10584 ≤ _ ∧ _ + w / 8 ≤
        sp.toNat - 10584 + (sp.toNat + 8 - (sp.toNat - 10584)) ∧ _ + w / 8 ≤ 2 ^ 64
      rw [offNat]
      omega
    exact (memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.right_sub retSrc fit)).trans
      (f4.memLoad_eq (outsideOutput call inside))
  obtain ⟨readGot, targetGot⟩ := Sec1.Wrapper.memcpy_target_load (image_of_frame call childFrame)
  obtain ⟨out, run, tag, rspOut, kept, written, prefixByte, encoded⟩ :=
    Serialize.serializerExecution (args := a) (mem := child) (sp := entry) (src := src) (dst := p)
      (ret := 0x102575) (point := pt)
      (by simp only [a, pointArgs, Vector.getElem_set, entryEq] <;> rfl)
      (by simp only [a, pointArgs, Vector.getElem_set, srcEq] <;> rfl)
      (by simp only [a, pointArgs, Vector.getElem_set] <;> rfl)
      (by simp only [a, pointArgs, Vector.getElem_set] <;> rfl)
      childDf childWidth childPoint srcRead pWrite (loEq ▸ loWrite) ret (by decide)
      (by omega) (by omega) (by omega) (by omega) readGot targetGot
  have writes : RamWriteFrame child out.store [⟨lo.toNat, 448⟩, ⟨p.toNat, 65⟩] := by
    simpa only [loEq] using written
  have within : RegionsWithin [⟨lo.toNat, 448⟩, ⟨p.toNat, 65⟩] (regions s).toList := by
    intro r hr
    refine ⟨Stack.region s signingKeyGenerateFromRng.minStackBytes,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rcases List.mem_cons.mp hr with rfl | rest
    · change sp.toNat - 10584 ≤ lo.toNat ∧ lo.toNat + 448 ≤
        sp.toNat - 10584 + (sp.toNat + 8 - (sp.toNat - 10584))
      omega
    · obtain rfl := List.mem_singleton.mp rest
      change sp.toNat - 10584 ≤ p.toNat ∧ p.toNat + 65 ≤
        sp.toNat - 10584 + (sp.toNat + 8 - (sp.toNat - 10584))
      omega
  have outFrame := childFrame.trans writes within
  have save {off : Nat} (small : off ≤ 16) :
      memLoad out.store (sp - BitVec.ofNat 64 off) 64 =
        memLoad mem (sp - BitVec.ofNat 64 off) 64 := by
    let addr := sp - BitVec.ofNat 64 off
    have addrNat : addr.toNat = sp.toNat - off := stackOffset call (by omega)
    have stackLow := call.stackAvailable.1
    change sp.toNat - 10584 + (sp.toNat + 8 - (sp.toNat - 10584)) < 2 ^ 32 at stackLow
    have outside : Outside [⟨lo.toNat, 448⟩, ⟨p.toNat, 65⟩] addr 8 := by
      refine ⟨by omega, fun r hr => Or.inr ?_⟩
      rcases List.mem_cons.mp hr with rfl | rest
      · change lo.toNat + 448 ≤ addr.toNat
        omega
      · obtain rfl := List.mem_singleton.mp rest
        change p.toNat + 65 ≤ addr.toNat
        omega
    refine (writes.memLoad_eq outside).trans ((memLoad_memStore_of_rangeApart _ _ _ _ _ ?_).trans
      (original f4 (off := off) (by omega)))
    change RangeApart entry 8 addr 8
    apply RangeApart.of_toNat <;> omega
  have mainKeep (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,15,22]) :
      out.values[i] = (Reg.ofIndex i).read s := by
    have ha : i.val ∈ [3,5,12,13,14,15,22] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have hk : i.val ∈ [3,5,12,13,14,15,22,39,50,51] :=
      List.mem_append_left [39,50,51] ha
    exact (kept i hk).trans ((eqArgs i ha).trans (f.kept i hi))
  have retSaved : memLoad out.store sp 64 = (returnBoundary s).rip := by
    have e := save (off := 0) (by decide)
    change memLoad out.store (sp - 0) 64 = memLoad mem (sp - 0) 64 at e
    rw [show sp - (0 : BitVec 64) = sp by bv_omega] at e
    exact e.trans f.ret
  have rspEq : entry + 8 = p := by rw [← entryEq]; bv_omega
  have frameOut : CallerFrame s out.values out.store :=
    ⟨rspOut.trans (congrArg (fun b => (⟨64,b⟩ : Value)) rspEq),
      mainKeep, (save (off := 16) (by decide)).trans f.rbx, (save (off := 8) (by decide)).trans f.r14,
      retSaved, outFrame⟩
  have scalarOut : atBytes dest 32 out.store (Encoding.natToOctets 32 d) := by
    have hsize : (Encoding.natToOctets 32 d).size = 32 := scalar.1
    have rd : Readable out.store dest 97 := ((outputWritable call).of_frame outFrame).readable
    have rd32 : Readable out.store dest 32 := rd.sub (b := dest) (Nat.le_refl _) (by omega)
    have copied : ∀ i < 4, memLoad out.store (wordAddr dest 64 i) 64 =
        memLoad mem (wordAddr p 64 i) 64 := by
      intro i hi
      have addrEq : (wordAddr dest 64 i).toNat = dest.toNat + 8 * i := by
        change (dest + BitVec.ofNat 64 (8 * i)).toNat = dest.toNat + 8 * i
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have sep := output_stack_apart call
      change dest.toNat + 97 ≤ sp.toNat - 10584 ∨ sp.toNat + 8 ≤ dest.toNat at sep
      have apart : RangeApart entry 8 (wordAddr dest 64 i) 8 := by
        apply RangeApart.of_toNat <;> omega
      have outside : Outside [⟨lo.toNat, 448⟩, ⟨p.toNat, 65⟩] (wordAddr dest 64 i) 8 := by
        refine ⟨by omega, fun r hr => ?_⟩
        rcases List.mem_cons.mp hr with rfl | rest
        · change _ ≤ lo.toNat ∨ lo.toNat + 448 ≤ _
          omega
        · obtain rfl := List.mem_singleton.mp rest
          change _ ≤ p.toNat ∨ p.toNat + 65 ≤ _
          omega
      exact (writes.memLoad_eq outside).trans
        ((memLoad_memStore_of_rangeApart _ _ _ _ _ apart).trans (copyWords p dest mem m4 rfl i hi))
    have copyView : ∀ i < 4, memLoad out.store (wordAddr dest 64 i) 64 =
        memLoad mem (wordAddr (BitVec.ofNat 64 p.toNat) 64 i) 64 := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact copied
    simpa only [hsize] using Common.hasBytes_of_word_copy (n := 4) scalar hsize rd32 copyView
  refine ⟨out.values, out.store, ?_, frameOut,
    (kept 3 (by decide)).trans ((eqArgs 3 (by decide)).trans dst), prefixByte, scalarOut, encoded⟩
  refine .step (b := ⟨⟨.l1215e0, a, child⟩, [Generator.callFrame .l102575 0x102575]⟩) ?_ ?_
  · simp only [Run, Program.sem, Program.step, block, Transfer.next]
  · exact ParseSignature.exec_reaches_resume run (Generator.callFrame .l102575 0x102575) []
      (by rw [tag]; rfl)

end K256.Proofs.Generate.Wrapper
