import K256.Proofs.Generate.Wrapper.Frame
import K256.Proofs.Generate.Wrapper.Scalar.Blocks
import K256.Proofs.Generate.Wrapper.Scalar.Octets

namespace K256.Proofs.Generate.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters K256.Proofs.Generate.LIR

variable {s : RamState} {random : ByteArray} {args : Vector Value Reg.count} {mem : Ram}

private theorem address_add (p : BitVec 64) (off : Nat) (low : p.toNat + off < 2^64) :
    (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt low]

private theorem stackForward (call : ValidCall signingKeyGenerateFromRng s [random])
    {base off : Nat} (depth : base ≤ 10584) (inside : off ≤ base) :
    (s.regValue .rsp - BitVec.ofNat 64 base + BitVec.ofNat 64 off).toNat =
      (s.regValue .rsp).toNat - base + off := by
  have sp : (s.regValue .rsp - BitVec.ofNat 64 base).toNat = (s.regValue .rsp).toNat - base :=
    stackOffset call depth
  have room : 10584 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  rw [address_add _ _ (by rw [sp]; have := (s.regValue .rsp).isLt; omega), sp]

private theorem writeScalarWords_frame {base : BitVec 64} {word : Nat → BitVec 64}
    {start : Ram} {region : MemoryRegion} (n : Nat)
    (within : ∀ i < n, InRegion region (wordAddr base 64 i) 8) :
    RamWriteFrame start (writeScalarWords base word start n) [region] := by
  induction n with
  | zero => exact RamWriteFrame.refl _ _
  | succ n ih =>
    exact (ih fun i hi => within i (by omega)).memStore _
      ⟨region, List.mem_cons_self, within n (by omega)⟩

private theorem writeScalarWords_read {base : BitVec 64} {word : Nat → BitVec 64}
    {start : Ram} {n : Nat} (low : base.toNat + 8 * n ≤ 2^32) :
    ∀ i < n, memLoad (writeScalarWords base word start n) (wordAddr base 64 i) 64 = word i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    change memLoad (memStore (writeScalarWords base word start n) (wordAddr base 64 n) (word n))
      (wordAddr base 64 i) 64 = word i
    rcases Nat.lt_or_eq_of_le (show i ≤ n by omega) with lt | rfl
    · have addr (j : Nat) (hj : j ≤ n) :
          (wordAddr base 64 j).toNat = base.toNat + 8 * j :=
        address_add base (8 * j) (by omega)
      have apart : RangeApart (wordAddr base 64 n) 8 (wordAddr base 64 i) 8 := by
        apply RangeApart.of_toNat <;> simp only [addr n (by omega), addr i (by omega)] <;> omega
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart]
      exact ih (by omega) i lt
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem scalar {d : Nat} {point : Curve.Point}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (key : KeyReady s random args mem d point) :
    ∃ a m, Segment .l102539 args mem .l102544 a m ∧ CallerFrame s a m ∧
      a[3] = ⟨64, s.regValue .rdi⟩ ∧ a[14].width = 64 ∧
      Sec1.Parser.PublicKeyAt m (s.regValue .rsp - 160) point ∧
      atBytes (s.regValue .rsp - 280) 32 m (Encoding.natToOctets 32 d) := by
  let sp := s.regValue .rsp
  let slot := sp - 288
  let dst := sp - 280
  let src := sp - 192
  let pushed := memStore mem slot (0x102544 : BitVec 64)
  let word (i : Nat) := bswapSpec (BitVec.ofNat 64 (d / 2 ^ (64 * (3 - i))))
  let stage := writeScalarWords dst word pushed
  let buffer : MemoryRegion := ⟨dst.toNat, 32⟩
  let scratch : MemoryRegion := ⟨slot.toNat, 40⟩
  have slotNat : slot.toNat = sp.toNat - 288 := stackOffset call (by decide)
  have dstNat : dst.toNat = sp.toNat - 280 := stackOffset call (by decide)
  have room : 10584 ≤ sp.toNat := call.stackAvailable.2.2.1
  have top : sp.toNat + 8 ≤ 2^64 := by
    have h := (stackRange (off := 0) (len := 8) call (by decide) (by decide)).2.2
    change (sp - 0#64).toNat + 8 ≤ 2^64 at h
    simpa only [BitVec.sub_zero] using h
  have slotRange : InRegion scratch slot 8 := ⟨Nat.le_refl _, Nat.add_le_add_left (by decide : 8 ≤ 40) _, by omega⟩
  have pushFrame : RamWriteFrame mem pushed [scratch] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨scratch, List.mem_cons_self, slotRange⟩
  have pushOk : StoreOk Extracted.programImage mem slot 8 0x10253f 5 := by
    apply ParseSignature.storeOk_of_codeRange (off := 6)
      ((stackWritable (off := 288) (len := 8) call (by decide) (by decide) (by decide)).of_frame key.writes)
      (fun x hx => Common.fnCode_subset_programImage x (code_l102539 x hx)) (by decide)
  have sourceAddr (j : Nat) (hj : j < 4) :
      (wordAddr src 64 j).toNat = sp.toNat - 192 + 8 * j :=
    stackForward (base := 192) (off := 8 * j) call (by decide) (by omega)
  have destAddr (j : Nat) (hj : j < 4) :
      (wordAddr dst 64 j).toNat = dst.toNat + 8 * j := by
    rw [dstNat]
    exact stackForward (base := 280) (off := 8 * j) call (by decide) (by omega)
  have intoBuffer : ∀ n ≤ 4, RamWriteFrame pushed (stage n) [buffer] := by
    intro n hn
    apply writeScalarWords_frame n
    intro j hj
    have h := destAddr j (by omega)
    change dst.toNat ≤ _ ∧ _ ≤ dst.toNat + 32 ∧ _
    rw [h]
    omega
  have baseWritable : Writable Extracted.programImage pushed dst 32 := ((stackWritable (off := 280) (len := 32) call (by decide) (by decide)
    (by decide)).of_frame key.writes).of_frame pushFrame
  have destWritable (j : Nat) (hj : j < 4) :
      Writable Extracted.programImage (stage j) (wordAddr dst 64 j) 8 := by
    have h := destAddr j hj
    exact (baseWritable.of_frame (intoBuffer j (by omega))).sub (by rw [h]; omega) (by rw [h]; omega)
  have stores (j off len : Nat) (hj : j < 4) (hlen : off + len ≤ bytes_l109e30.length) :
      StoreOk Extracted.programImage (stage j) (wordAddr dst 64 j) 8
        (0x109e30 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange (destWritable j hj)
      (fun x hx => Common.fnCode_subset_programImage x (code_l109e30 x hx)) hlen
  have srcReadable : Readable pushed src 32 := (((stackWritable (off := 192) (len := 32) call (by decide) (by decide)
    (by decide)).of_frame key.writes).of_frame pushFrame).readable
  have load (j : Nat) (hj : j < 4) : LoadOk pushed (wordAddr src 64 j) 8 := by
    have h := sourceAddr j hj
    have srcNat : src.toNat = sp.toNat - 192 := stackOffset call (by decide)
    exact LoadOk.of_region srcReadable (by rw [h, srcNat]; omega) (by rw [h, srcNat]; omega)
  have fromLimbs (j : Nat) (hj : j < 4) :
      bswapSpec (memLoad pushed (wordAddr src 64 (3 - j)) 64) = word j := by
    have index : 3 - j < 4 := by omega
    change bswapSpec (memLoad pushed (wordAddr src 64 (3 - j)) 64) =
      bswapSpec (BitVec.ofNat 64 (d / 2 ^ (64 * (3 - j))))
    congr 1
    rw [pushFrame.memLoad_eq (a := wordAddr src 64 (3 - j)) (k := 64)]
    · exact (key.limbs (3 - j) index).trans (Vector.getElem_ofFn _)
    · have h := sourceAddr (3 - j) index
      refine ⟨by rw [h]; omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inr (by change slot.toNat + 40 ≤ _; rw [slotNat, h]; omega)
  have scratchWrites : RamWriteFrame mem (stage 4) [scratch] :=
    pushFrame.trans (intoBuffer 4 (by decide)) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨scratch, List.mem_cons_self, ?_, ?_⟩
      · change slot.toNat ≤ dst.toNat
        omega
      · change dst.toNat + 32 ≤ slot.toNat + 40
        omega)
  have retOk : LoadOk (stage 4) slot 8 :=
    let rd := ((stackWritable (off := 288) (len := 8) call (by decide) (by decide)
      (by decide)).of_frame key.writes).readable.of_frame scratchWrites
    ⟨rd.low, rd.present⟩
  have retTag : memLoad (stage 4) slot 64 = 0x102544 := by
    rw [(intoBuffer 4 (by decide)).memLoad_eq (a := slot) (k := 64)]
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · refine ⟨by omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inl (by change slot.toNat + 8 ≤ dst.toNat; omega)
  have dst₀ : wordAddr dst 64 0 = dst := BitVec.add_zero dst
  have childRsp : (scalarCallArgs args sp)[4].get 64 = slot := by
    simp only [scalarCallArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    rfl
  have childRsi : (scalarCallArgs args sp)[6].get 64 = src := by
    simp only [scalarCallArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    rfl
  have childRdi : (scalarCallArgs args sp)[7].get 64 = dst := by
    simp only [scalarCallArgs, Vector.getElem_set, ↓reduceIte]
    rfl
  obtain ⟨out, leaf, tag, memory, rsp, preserved⟩ := scalarReturnBlock
    (a := scalarCallArgs args sp) (mem := pushed) (word := word)
    (sp := slot) (dst := dst) (src := src) childRsp childRsi childRdi load fromLimbs
    (by rw [← dst₀]; exact stores 0 30 3 (by decide) (by decide))
    (stores 1 33 4 (by decide) (by decide)) (stores 2 37 4 (by decide) (by decide))
    (stores 3 41 4 (by decide) (by decide)) retOk retTag
  let fr := Generator.callFrame .l102544 0x102544
  let resumed := fr.resume out
  have kept (i : Fin Reg.count) (hi : i.val ∈ [3, 5, 12, 13, 14, 15, 22]) :
      resumed.arguments[i] = args[i] := by
    change resumed.arguments[i.val] = args[i.val]
    simp only [resumed, StackFrame.resume, fr, Generator.callFrame, Vector.getElem_cast,
      Vector.getElem_append_left i.isLt]
    refine (preserved i hi).trans ?_
    change (scalarCallArgs args sp)[i.val] = args[i.val]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    have h4 : 4 ≠ i.val := by omega
    have h6 : 6 ≠ i.val := by omega
    have h7 : 7 ≠ i.val := by omega
    simp only [scalarCallArgs, Vector.getElem_set, h4, h6, h7, ↓reduceIte]
  have reaches : Segment .l102539 args mem .l102544 resumed.arguments (stage 4) := by
    apply Star.step (b := ⟨⟨.l109e30, scalarCallArgs args sp, pushed⟩, [fr]⟩)
    · change (program.runBlock _ _).next _ [] = _
      rw [scalarCallBlock key.rsp key.key pushOk]
      rfl
    · apply Semantics.Reaches.single
      change (program.runBlock _ _).next _ [fr] = _
      rw [leaf]
      change (if fr.Accepts (dialect Extracted.programImage) out.tag then
        Outcome.next ⟨resumed, []⟩ else Outcome.stuck) = _
      rw [tag]
      have accept : fr.Accepts (dialect Extracted.programImage) (some ⟨64, 0x102544⟩) = true := rfl
      rw [accept]
      change Outcome.next ⟨resumed, []⟩ = _
      change out.store = stage 4 at memory
      rw [← memory]
      rfl
  have beyondScratch (base off width : Nat) (hb : base ≤ 248) (ho : off ≤ base)
      (fits : off + width / 8 ≤ base + 8) :
      memLoad (stage 4) (sp - BitVec.ofNat 64 base + BitVec.ofNat 64 off) width =
        memLoad mem (sp - BitVec.ofNat 64 base + BitVec.ofNat 64 off) width := by
    apply scratchWrites.memLoad_eq
    have h := stackForward call (base := base) (off := off) (by omega) ho
    change (sp - BitVec.ofNat 64 base + BitVec.ofNat 64 off).toNat = sp.toNat - base + off at h
    refine ⟨by change _ + width / 8 ≤ 2^64; rw [h]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change slot.toNat + 40 ≤ _; rw [slotNat, h]; omega)
  have affine : Sec1.Parser.PublicKeyAt (stage 4) (sp - 160) point := by
    obtain ⟨x, y, eq, original⟩ := key.affine
    exact ⟨x, y, eq, original.of_copy (fun off width h => beyondScratch 160 off width (by decide)
      (by omega) (by omega))⟩
  have stackF : RamWriteFrame s.external (stage 4) [Stack.region s signingKeyGenerateFromRng.minStackBytes] :=
    key.writes.trans scratchWrites (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      have h := stackRange (off := 288) (len := 40) call (by decide) (by decide)
      exact ⟨_, List.mem_cons_self, h.1, h.2.1⟩)
  have finalFrame : RamWriteFrame s.external (stage 4) (regions s).toList :=
    ⟨fun x h => stackF.outside x ⟨h.1, fun r hr => h.2 r (List.mem_cons_of_mem _ hr)⟩, stackF.present⟩
  have caller : CallerFrame s resumed.arguments (stage 4) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, finalFrame⟩
    · change out.values[4] = _
      rw [rsp, show slot + 8 = dst by dsimp only [slot, dst]; bv_omega]
    · intro i hi
      have hs : i.val ∈ [3, 5, 12, 13, 14, 15, 22] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        rcases hi with h | h | h | h | h <;> simp only [h, true_or, or_true]
      exact (kept i hs).trans (key.kept i hi)
    · have h := beyondScratch 16 0 64 (by decide) (by decide) (by decide)
      change memLoad (stage 4) (sp - 16 + 0#64) 64 = memLoad mem (sp - 16 + 0#64) 64 at h
      rw [BitVec.add_zero] at h
      exact h.trans key.rbx
    · have h := beyondScratch 8 0 64 (by decide) (by decide) (by decide)
      change memLoad (stage 4) (sp - 8 + 0#64) 64 = memLoad mem (sp - 8 + 0#64) 64 at h
      rw [BitVec.add_zero] at h
      exact h.trans key.r14
    · have h := beyondScratch 0 0 64 (by decide) (by decide) (by decide)
      change memLoad (stage 4) (sp - 0#64 + 0#64) 64 = memLoad mem (sp - 0#64 + 0#64) 64 at h
      rw [BitVec.add_zero, BitVec.sub_zero] at h
      exact h.trans key.ret
  refine ⟨_, stage 4, reaches, caller, (kept ⟨3, by decide⟩ (by decide)).trans key.dst,
    congrArg Value.width ((kept ⟨14, by decide⟩ (by decide)).trans key.key), affine, ?_⟩
  apply scalarOctets
  · intro j hj
    rw [Vector.getElem_ofFn]
    exact writeScalarWords_read baseWritable.readable.low j hj
  · exact baseWritable.readable.of_frame (intoBuffer 4 (by decide))

end K256.Proofs.Generate.Wrapper
