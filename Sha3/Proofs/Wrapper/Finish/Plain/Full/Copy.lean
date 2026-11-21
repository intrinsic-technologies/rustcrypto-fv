import Sha3.Proofs.Wrapper.Finish.Plain.Full.CopyGlue
import Sha3.Proofs.Wrapper.Finish.Plain.Call
import Sha3.Proofs.Wrapper.Finish.Final
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Memcpy

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem full_register_call [bindings : Bindings] {initial s : RamState} {mode : Mode}
    {inputs : Array Input} {split : Nat} {p : BitVec 64}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial .sha256 mode true true)
    (image : ImageAt p (if mode = .digest then [0x41, 0xff, 0xd4] else [0xff, 0xd3]))
    (target : (Operand.reg (if mode = .digest then 12 else 3) : Operand 64).read s = 0x106a70) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial .sha256 mode t true true ∧
      t.RIP = 0x106a70 ∧ stackPtr t = frameBase initial .sha256 mode true true - 8 ∧
      stackTop t = p + (if mode = .digest then 3 else 2 : BitVec 64) ∧
      AgreesExcept [.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] s t ∧
      (callEffect (fun _ ↦ (0x106a70 : BitVec 64))
        (p + (if mode = .digest then 3 else 2 : BitVec 64)) s).Holds s t := by
  have budget : mode.frameSize .sha256 true true + 8 ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true]; omega
  have align : mode.frameSize .sha256 true true % 8 = 0 := by
    rcases hm with rfl | rfl <;> decide
  have heq : 8 * (mode.frameSize .sha256 true true / 8) = mode.frameSize .sha256 true true := by omega
  have hmem := stack_push_readable_after (n := mode.frameSize .sha256 true true / 8)
    inv hCall.stackAvailable (by omega) (by simpa only [heq, frameBase] using sp)
  have result : Machine.step s = some (.next (afterStep s (if mode = .digest then 3 else 2) fun t ↦
      callState (callFrom false t (p + (if mode = .digest then 3 else 2 : BitVec 64)))
        (p + (if mode = .digest then 3 else 2 : BitVec 64)) 0x106a70)) := by
    rcases hm with rfl | rfl
    · change (Operand.reg 3 : Operand 64).read s = 0x106a70 at target
      have hc := image.code inv.loaded
      have hs := call_r64_step_of_readable s inv.ready [] (by simp) (by simp) rfl rfl rfl
        0xd3 (by decide) (by decide) (ip.symm ▸ hc.bytesAt)
        (ip.symm ▸ hc.low (by decide) (by decide))
        (by change ((Operand.reg 3 : Operand 64).read s).toNat < 2^32; rw [target]; decide)
        hmem.1 hmem.2
      change Machine.step s = some (.next (afterStep s 2 fun t ↦
        callState (callFrom false t (BitVec.add s.RIP (BitVec.ofNat 64 2))) (BitVec.add s.RIP (BitVec.ofNat 64 2)) ((Operand.reg 3 : Operand 64).read s))) at hs
      simp only [reduceCtorEq, ↓reduceIte]
      rw [ip, target] at hs
      exact hs
    · change (Operand.reg 12 : Operand 64).read s = 0x106a70 at target
      have hc := image.code inv.loaded
      have hr : RexPrefix (0x41 : UInt8).toBitVec := by unfold RexPrefix; decide
      have hs := call_r64_step_of_readable s inv.ready [0x41]
        (by simpa using hr.scanPrefix) (by decide)
        (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl)
        0xd4 (by decide) (by decide) (ip.symm ▸ hc.bytesAt)
        (ip.symm ▸ hc.low (by decide) (by decide))
        (by rw [scanContext_rex _ _ hr]; change ((Operand.reg 12 : Operand 64).read s).toNat < 2^32; rw [target]; decide)
        hmem.1 hmem.2
      simp only [scanContext_rex _ _ hr] at hs
      change Machine.step s = some (.next (afterStep s 3 fun t ↦
        callState (callFrom false t (BitVec.add s.RIP (BitVec.ofNat 64 3))) (BitVec.add s.RIP (BitVec.ofNat 64 3)) ((Operand.reg 12 : Operand 64).read s))) at hs
      simp only [↓reduceIte]
      rw [ip, target] at hs
      exact hs
  obtain ⟨t, ht, it, pt, st, rt, agt, et⟩ := callAt (mode.frameSize .sha256 true true)
    (if mode = .digest then 3 else 2) false
    (p + (if mode = .digest then 3 else 2 : BitVec 64)) 0x106a70 hCall budget inv sp result
  rw [← frameBase_sub_eight initial .sha256 mode true true] at st agt
  exact ⟨t, ht, it, pt, st, rt, agt, et⟩


theorem full_copy_call [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {mode : Mode} {inputs : Array Input} {split offset : Nat}
    {p dst : BitVec 64} {bytes : Vector UInt8 200}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial .sha256 mode true true)
    (image : ImageAt p (if mode = .digest then [0x41, 0xff, 0xd4] else [0xff, 0xd3]))
    (target : (Operand.reg (if mode = .digest then 12 else 3) : Operand 64).read s = 0x106a70)
    (hdst : (Operand.reg 7 : Operand 64).read s = dst)
    (hsrc : (Operand.reg 6 : Operand 64).read s = frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset)
    (hlen : (Operand.reg 2 : Operand 64).read s = 200)
    (hOffset : offset + 200 ≤ mode.frameSize .sha256 true true + 8)
    (hDst : MemReadable s dst 200)
    (hSep : (frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset).toNat + 200 ≤ dst.toNat ∨
      dst.toNat + 200 ≤ (frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset).toNat)
    (hWrites : ∀ i < 200, ∃ region ∈ writeRegions initial .sha256 mode true true,
      region.Contains (dst + BitVec.ofNat 64 i).toNat)
    (hApart : RangeApart dst 200 (frameBase initial .sha256 mode true true - 8) 8)
    (hLow : (p + (if mode = .digest then 3 else 2 : BitVec 64)).toNat < 2^32)
    (hBytes : ∀ i : Fin 200, s.external[frameBase initial .sha256 mode true true +
      BitVec.ofNat 64 offset + BitVec.ofNat 64 i.val]? = some bytes[i]) :
    ∃ t, Advances (returnBoundary initial) (1 + Memcpy.memcpy200Steps dst) s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = p + (if mode = .digest then 3 else 2 : BitVec 64) ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      (∀ i : Fin 200, t.external[dst + BitVec.ofNat 64 i.val]? = some bytes[i]) ∧
      AgreesExcept ([.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] ++
        Memcpy.clobbers dst 200) s t := by
  obtain ⟨c, hc, ic, pc, sc, rc, ac, ec⟩ := full_register_call hm hCall inv ip sp image target
  have cdst : (Operand.reg 7 : Operand 64).read c = dst := (ac.read (by simp)).trans hdst
  have csrc : (Operand.reg 6 : Operand 64).read c = frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset :=
    (ac.read (by simp)).trans hsrc
  have clen : (Operand.reg 2 : Operand 64).read c = 200 := (ac.read (by simp)).trans hlen
  have budget : mode.frameSize .sha256 true true + 8 ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true]; omega
  have stackRead : MemReadable c (frameBase initial .sha256 mode true true - 8) 8 := by
    rw [frameBase_sub_eight initial .sha256 mode true true]
    have hl := stack_sub_low hCall.stackAvailable budget
    change (initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize .sha256 true true + 8)).toNat +
      (mode.frameSize .sha256 true true + 8) < 2^32 at hl
    refine ⟨by omega, ?_⟩
    intro i hi
    exact ic.grows _ (Option.isSome_iff_exists.mpr (stack_sub_allocated hCall.stackAvailable budget (by omega)))
  have pre : Memcpy.Pre (returnBoundary initial) c 200 false := by
    refine ⟨pc, clen, trivial, ic.direction, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [csrc]; exact ic.frameReadable hCall.stackAvailable hOffset
    · rw [cdst]; exact hDst.of_agreesExcept ac
    · rw [csrc, cdst]; exact hSep
    · rw [cdst]
      intro address ha ht
      obtain ⟨i, hi, rfl⟩ := Finalize.region_contains_offset ha
      obtain ⟨r, hr, hc⟩ := hWrites i hi
      exact writeRegions_avoid hCall r hr _ hc (.inr ht)
    · rw [cdst]
      intro address ha ht
      obtain ⟨i, hi, rfl⟩ := Finalize.region_contains_offset ha
      obtain ⟨r, hr, hc⟩ := hWrites i hi
      exact writeRegions_avoid hCall r hr _ hc (.inl ht)
    · rw [sc]; exact stackRead
    · rw [rc]; exact hLow
    · rw [cdst, sc]; exact hApart
    · rw [sc, frameBase_sub_eight initial .sha256 mode true true]
      apply stackSub_ne_returnBoundary
      rcases hm with rfl | rfl <;> decide
    · right
      rw [sc, BitVec.sub_add_cancel]
      apply stackSub_ne_returnBoundary
      rcases hm with rfl | rfl <;> decide
  obtain ⟨t, ht, dt⟩ := Memcpy.memcpy200_steps hStride (returnBoundary initial) c ic.ready ic.code pre
  change Advances (returnBoundary initial) (Memcpy.memcpy200Steps ((Operand.reg 7 : Operand 64).read c)) c t at ht
  rw [cdst] at ht
  have ag := dt.agrees
  rw [cdst] at ag
  refine ⟨t, hc.trans ht, ic.of_agreesExcept hCall dt.ready ag
    (Memcpy.clobbers_writesWithin hWrites) (by simp [Memcpy.clobbers]), dt.rip.trans rc,
    dt.rsp.trans (by rw [sc, BitVec.sub_add_cancel]), ?_, ac.trans ag⟩
  intro i
  have hb := dt.copy i.val i.isLt
  rw [cdst, csrc] at hb
  rw [hb]
  have hmem := callMemory_above ec (offset := offset) (count := 200)
    (by have hf : mode.frameSize .sha256 true true ≤ 664 := by rcases hm with rfl | rfl <;> decide
        omega) i.val i.isLt
  rw [sp] at hmem
  exact hmem.trans (hBytes i)


theorem full_copy_saved {initial s t : RamState} {mode : Mode} {dst : BitVec 64}
    (hm : mode = .plain ∨ mode = .digest)
    (saved : SavedFrame initial s mode true)
    (ag : AgreesExcept ([.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] ++
      Memcpy.clobbers dst 200) s t)
    (apart : RangeApart dst 200
      (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount true)) (8 * mode.pushCount true + 8)) :
    SavedFrame initial t mode true := by
  have keep (i : Fin (mode.pushCount true + 1)) :
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount true) + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read t =
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount true) + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s := by
    apply readMem_agrees ag
    intro j hj c hc hcover
    simp only [Memcpy.clobbers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      try exact hcover.elim
    · obtain ⟨k, hk, he⟩ := hcover
      have hSep : OffsetsApart (-BitVec.ofNat 64 (mode.frameSize .sha256 true true + 8)) 8
          (-BitVec.ofNat 64 (8 * mode.pushCount true) + BitVec.ofNat 64 (8 * i.val)) 8 := by
        rcases hm with rfl | rfl <;>
          exact (by unfold OffsetsApart; decide +kernel : ∀ i : Fin (_ + 1), OffsetsApart _ 8
            (-BitVec.ofNat 64 _ + BitVec.ofNat 64 (8 * i.val)) 8) i
      apply hSep.ne (initial.regValue .rsp) hk hj (by decide)
      rw [frameBase_sub_eight initial .sha256 mode true true] at he
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using he.symm
    · obtain ⟨k, hk, he⟩ := hcover
      apply apart k hk (8 * i.val + j) (by have := i.isLt; omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
  refine ⟨fun i ↦ (keep ⟨i.val, by omega⟩).trans (saved.saved i), ?_⟩
  have h := keep ⟨mode.pushCount true, by omega⟩
  simp only [BitVec.sub_add_cancel] at h
  exact h.trans saved.returnSlot


theorem full_copy_saved_apart {initial : RamState} {mode : Mode} {dst : BitVec 64}
    (hm : mode = .plain ∨ mode = .digest)
    (hs : Stack.Valid initial (mode.entry .sha256 true true).minStackBytes)
    (hd : dst.toNat + 200 ≤ 2^32)
    (ha : (MemoryRegion.mk dst.toNat 200).Disjoint (Stack.region initial (mode.entry .sha256 true true).minStackBytes) ∨
      dst.toNat + 200 ≤ (initial.regValue .rsp).toNat - 8 * mode.pushCount true) :
    RangeApart dst 200 (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount true)) (8 * mode.pushCount true + 8) := by
  have budget : 8 * mode.pushCount true ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true]
    rcases hm with rfl | rfl <;> decide
  have hu := hs.2.2.1
  change (mode.entry .sha256 true true).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
  have hl := hs.1
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded, userAddressLimit] at hl
  have hn := stack_sub_toNat hs.2.2.1 budget
  intro i hi j hj he
  have ni : (dst + BitVec.ofNat 64 i).toNat = dst.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have nj : (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount true) + BitVec.ofNat 64 j).toNat =
      (initial.regValue .rsp).toNat - 8 * mode.pushCount true + j := by
    rw [BitVec.toNat_add, hn, BitVec.toNat_ofNat]; omega
  have he' := congrArg BitVec.toNat he
  rw [ni, nj] at he'
  rcases ha with ha | ha
  · apply ha (dst.toNat + i) (by change dst.toNat ≤ _ ∧ _ < dst.toNat + 200; omega)
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains]
    omega
  · omega

theorem full_copy_frame {initial s t : RamState} {mode : Mode} {dst out : BitVec 64}
    (hs : Stack.Valid initial (mode.entry .sha256 true true).minStackBytes)
    (ag : AgreesExcept ([.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] ++ Memcpy.clobbers dst 200) s t)
    (hd : ∀ i < 200, ∃ r ∈ finalWrites initial .sha256 mode out true true,
      r.Contains (dst + BitVec.ofNat 64 i).toNat) :
    MemoryWriteFrame s t (finalWrites initial .sha256 mode out true true) := by
  apply ag.memoryWriteFrame
  intro c hc address hcover
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    rw [frameBase_sub_eight initial .sha256 mode true true]
    exact stack_sub_contains hs (by rw [Mode.stackBudget mode .sha256 true true]; omega) (by omega)
  · exact Memcpy.clobbers_writesWithin hd c hc address hcover


theorem full_copy_advance [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {mode : Mode} {inputs : Array Input} {split : Nat}
    {out : BitVec 64} {bytes : Vector UInt8 200}
    (hm : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (saved : SavedFrame initial s mode true)
    (ip : s.RIP = callAddress mode .sha256 true true + (5 : BitVec 64))
    (sp : stackPtr s = frameBase initial .sha256 mode true true)
    (hTemp : s.regValue .r14 = frameBase initial .sha256 mode true true +
      BitVec.ofNat 64 (if mode = .digest then 408 else 416))
    (hOutput : (outputOperand initial .sha256 mode true true).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, 200⟩)
    (hMember : (⟨out.toNat, 200⟩ : MemoryRegion) ∈ writeRegions initial .sha256 mode true true)
    (hApart : (⟨out.toNat, 200⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes))
    (hBytes : ∀ i : Fin 200, s.external[frameBase initial .sha256 mode true true +
      BitVec.ofNat 64 (if mode = .digest then 408 else 416) + BitVec.ofNat 64 i.val]? = some bytes[i]) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial .sha256 mode t true true ∧ SavedFrame initial t mode true ∧
      t.RIP = epilogueAddress mode .sha256 true true ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      (∀ i : Fin 200, t.external[out + BitVec.ofNat 64 i.val]? = some bytes[i]) ∧
      MemoryWriteFrame s t (finalWrites initial .sha256 mode out true true) ∧
      t.regValue .rbp = s.regValue .rbp := by
  have outLow : out.toNat + 200 < 2^32 := hOut.2.1
  let cp : Nat := if mode = .digest then 208 else 216
  let tp : Nat := if mode = .digest then 408 else 416
  let base := frameBase initial .sha256 mode true true
  have cv : BitVec.ofNat 64 cp = (if mode = .digest then 208 else 216 : BitVec 64) := by
    dsimp only [cp]; split <;> rfl
  have tv : BitVec.ofNat 64 tp = (if mode = .digest then 408 else 416 : BitVec 64) := by
    dsimp only [tp]; split <;> rfl
  have bounds : 208 ≤ cp ∧ cp + 200 = tp ∧ tp + 200 + 8 * mode.pushCount true ≤
      mode.frameSize .sha256 true true ∧ mode.frameSize .sha256 true true ≤ 664 := by
    rcases hm with rfl | rfl <;> decide
  have budget : mode.frameSize .sha256 true true ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true]; omega
  have natOffset (k : Nat) (hk : k ≤ mode.frameSize .sha256 true true + 8) :
      (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
    frameAddress_toNat hCall.stackAvailable budget hk
  have stackOffset (k : Nat) (hk : k < mode.frameSize .sha256 true true + 8) :
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).Contains (base + BitVec.ofNat 64 k).toNat :=
    frameAddress_contains hCall.stackAvailable budget hk
  have cpSaved : RangeApart (base + BitVec.ofNat 64 cp) 200
      (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount true)) (8 * mode.pushCount true + 8) := by
    apply full_copy_saved_apart hm hCall.stackAvailable
    · exact (inv.frameReadable hCall.stackAvailable (offset := cp) (by omega)).low
    · right
      rw [natOffset cp (by omega)]
      have hb : base.toNat = (initial.regValue .rsp).toNat - mode.frameSize .sha256 true true :=
        stack_sub_toNat hCall.stackAvailable.2.2.1 budget
      rw [hb]
      have hu := hCall.stackAvailable.2.2.1
      change (mode.entry .sha256 true true).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
      omega
  have cpStack : RangeApart (base + BitVec.ofNat 64 cp) 200 (base - 8) 8 := by
    have h := RangeApart.offsets (base - 8) (a := 8 + cp) (b := 0) (len := 200) (count := 8)
      (by omega) (by decide) (.inr (by omega))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel, BitVec.add_zero] using h
  have cpWrites (i : Nat) (hi : i < 200) :
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).Contains
        (base + BitVec.ofNat 64 cp + BitVec.ofNat 64 i).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact stackOffset _ (by omega)
  obtain ⟨a, ha, ia, pa, sa, a15, atarget, alen, adst, asrc, aa⟩ :=
    full_copy_prefix hm hCall inv ip sp (by simpa only [← tv] using hTemp)
  rw [← cv] at a15
  rw [← tv] at asrc
  have amem : a.external = s.external := aa.external (by simp [Component.Covers])
  have savedA : SavedFrame initial a mode true := saved.of_localFrame (v := .sha256)
    (keccak := true) aa (by simp [Component.Covers])
  have outA : (outputOperand initial .sha256 mode true true).read a = out := by
    rcases hm with rfl | rfl
    · simpa only [outputOperand, Operand.read, amem] using hOutput
    · exact (aa.read (r := 3) (n := 64) (by decide)).trans hOutput
  obtain ⟨b, hab, ib, pb, sb, bbytes, ab⟩ := full_copy_call hStride hm hCall ia pa sa
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    atarget (adst.trans a15) asrc alen (by omega)
    (ia.frameReadable hCall.stackAvailable (offset := cp) (by omega))
    (.inr (by rw [natOffset cp (by omega), natOffset tp (by omega)]; omega))
    (fun i hi ↦ ⟨_, stack_mem_writeRegions initial .sha256 mode true true, cpWrites i hi⟩)
    cpStack (by rcases hm with rfl | rfl <;> decide +kernel)
    (fun i ↦ by rw [amem]; exact hBytes i)
  have savedB := full_copy_saved hm savedA ab cpSaved
  have outB : (outputOperand initial .sha256 mode true true).read b = out := by
    rcases hm with rfl | rfl
    · apply Eq.trans (b := (outputOperand initial .sha256 .plain true true).read a) ?_ outA
      simp only [outputOperand, outputSlot, Mode.outputSlotOffset, BitVec.add_zero]
      change (Operand.mem base : Operand 64).read b = (Operand.mem base : Operand 64).read a
      apply readMem_agrees ab
      intro i hi c hc hcover
      simp only [Memcpy.clobbers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        try exact hcover.elim
      · obtain ⟨j, hj, he⟩ := hcover
        have sep := RangeApart.offsets (base - 8) (a := 0) (b := 8) (len := 8) (count := 8)
          (by decide) (by decide) (.inl (by decide))
        apply sep j hj i hi
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.sub_add_cancel] using he.symm
      · obtain ⟨j, hj, he⟩ := hcover
        have sep := RangeApart.offsets base (a := cp) (b := 0) (len := 200) (count := 8)
          (by decide) (by decide) (.inr (by decide))
        apply sep j hj i hi
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm
    · exact (ab.read (r := 3) (n := 64) (by simp [Memcpy.clobbers])).trans outA
  have b15 : b.regValue .r15 = base + BitVec.ofNat 64 cp :=
    (ab.read (r := 15) (n := 64) (by simp [Memcpy.clobbers])).trans a15
  have btarget : (Operand.reg (fullCopyTargetReg mode) : Operand 64).read b = 0x106a70 :=
    (ab.read (by rcases hm with rfl | rfl <;> simp [Memcpy.clobbers, fullCopyTargetReg])).trans atarget
  have pb' : b.RIP = fullCopySuffixPC mode := by
    rcases hm with rfl | rfl <;> exact pb
  obtain ⟨c, hbc, ic, pc, sc, cdst, csrc, clen, ac⟩ := full_copy_suffix hm hCall ib pb' sb outB
  have cmem : c.external = b.external := ac.external (by simp [Component.Covers])
  have savedC := savedB.of_localFrame (v := .sha256) (keccak := true) ac (by simp [Component.Covers])
  have ctarget : (Operand.reg (fullCopyTargetReg mode) : Operand 64).read c = 0x106a70 :=
    (ac.read (by rcases hm with rfl | rfl <;> simp [fullCopyTargetReg])).trans btarget
  have outStack : RangeApart out 200 (base - 8) 8 := by
    intro i hi j hj he
    apply hApart (out + BitVec.ofNat 64 i).toNat (Finalize.region_contains_byte (n := 200) (by omega) hi)
    rw [he, frameBase_sub_eight initial .sha256 mode true true]
    exact stack_sub_contains hCall.stackAvailable (by rw [Mode.stackBudget mode .sha256 true true]; omega) (by omega)
  have sepOut : (base + BitVec.ofNat 64 cp).toNat + 200 ≤ out.toNat ∨
      out.toNat + 200 ≤ (base + BitVec.ofNat 64 cp).toNat := by
    apply Classical.byContradiction
    intro hn
    have h1 : ¬ (base + BitVec.ofNat 64 cp).toNat + 200 ≤ out.toNat := fun h ↦ hn (.inl h)
    have h2 : ¬ out.toNat + 200 ≤ (base + BitVec.ofNat 64 cp).toNat := fun h ↦ hn (.inr h)
    let address := max out.toNat (base + BitVec.ofNat 64 cp).toNat
    apply hApart address (by change out.toNat ≤ address ∧ address < out.toNat + 200; dsimp only [address]; omega)
    have ha : (MemoryRegion.mk (base + BitVec.ofNat 64 cp).toNat 200).Contains address := by
      change _ ≤ address ∧ address < _; dsimp only [address]; omega
    exact digest_region_contains (v := .sha256) (fullState := true) hCall.stackAvailable (by change cp + 200 ≤ mode.frameSize .sha256 true true + 8; omega) ha
  have outRead : MemReadable c out 200 := by
    refine ⟨by omega, ?_⟩
    intro i hi
    exact ic.grows _ (Option.isSome_iff_exists.mpr
      (hOut.2.2 _ (Finalize.region_contains_byte (n := 200) (by omega) hi)))
  obtain ⟨t, hct, it, pt, st, tbytes, ct⟩ := full_copy_call hStride hm hCall ic pc sc
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    ctarget cdst (csrc.trans b15) clen (by omega) outRead sepOut
    (fun i hi ↦ ⟨_, hMember, Finalize.region_contains_byte (n := 200) (by omega) hi⟩)
    outStack (by rcases hm with rfl | rfl <;> decide +kernel)
    (fun i ↦ by rw [cmem]; exact bbytes i)
  have savedT := full_copy_saved hm savedC ct
    (full_copy_saved_apart hm hCall.stackAvailable (by omega) (.inl hApart))
  have memAB := full_copy_frame hCall.stackAvailable ab
    (out := out) (fun i hi ↦ ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, cpWrites i hi⟩)
  have memCT := full_copy_frame hCall.stackAvailable ct
    (out := out) (fun i hi ↦ ⟨_, Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩,
      Finalize.region_contains_byte (n := 200) (by omega) hi⟩)
  refine ⟨_, t, ha.trans (hab.trans (hbc.trans hct)), it, savedT, ?_, st, tbytes, ?_, ?_⟩
  · rcases hm with rfl | rfl <;> exact pt
  · exact memoryWriteFrame_trans (fun address hn ↦ by rw [amem])
      (memoryWriteFrame_trans memAB (memoryWriteFrame_trans (fun address hn ↦ by rw [cmem]) memCT))
  · exact (ct.read (r := 5) (n := 64) (by simp [Memcpy.clobbers])).trans
      ((ac.read (r := 5) (n := 64) (by decide)).trans
        ((ab.read (r := 5) (n := 64) (by simp [Memcpy.clobbers])).trans
          (aa.read (r := 5) (n := 64) (by rcases hm with rfl | rfl <;> decide))))

end Sha3.Proofs.Wrapper.Finish.Plain
