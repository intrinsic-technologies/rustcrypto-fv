import K256.Proofs.Ecdh.Output.Serialize.Setup
import K256.Proofs.Sec1.Serialize.PackExecution
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Sec1.Serialize.Coordinates.Normalize

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Common.Field

theorem packReturn {a : Values Value Reg.count} {m : Ram} {base dst bx : Word} {w : Limbs}
    (rsp : a[4] = ⟨64, base⟩) (rbx : a[3] = ⟨64, dst⟩) (r14 : a[14] = ⟨64, base + 48⟩)
    (df : a[22] = ⟨1, 0⟩) (win : Writable Extracted.programImage m (base - 121) 433)
    (dest : Writable Extracted.programImage m dst 32) (sep : base.toNat + 112 ≤ dst.toNat)
    (saved : memLoad m (base + 88) 64 = bx) (ret : memLoad m (base + 104) 64 = 0x101b1d)
    (words : WordsAt m (base + 48) 64 w) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l120398, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, 0x101b1d⟩ ∧ o.values[4] = ⟨64, base + 112⟩ ∧
      o.values[3] = ⟨64, bx⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      RamWriteFrame m o.store [⟨(base - 8).toNat, 8⟩, ⟨dst.toNat, 32⟩] ∧
      WordsAt o.store dst 64 (Sec1.Serialize.packWords w) := by
  have slot : Writable Extracted.programImage m (base - 8) 8 :=
    win.of_offsets (addr_sub base 8) (addr_sub base 121) (by decide)
  have ok : StoreOk Extracted.programImage m (base - 8) 8 0x12039e 5 :=
    ParseSignature.storeOk_of_codeRange (off := 6) slot
      (fun x hx => Common.fnCode_subset_programImage x (code_l120398 x hx)) (by decide)
  let pushed := memStore m (base - 8) (0x1203a3 : Word)
  have h4 : a[4].get 64 = base := by rw [rsp]; rfl
  have h3 : a[3].get 64 = dst := by rw [rbx]; rfl
  have h14 : a[14].get 64 = base + 48 := by rw [r14]; rfl
  have call : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l120398, a, m⟩ =
      .call ⟨.l1148d0, b, pushed⟩ (fieldReturn .l1203a3 0x1203a3) ∧
      b[4] = ⟨64, base - 8⟩ ∧ b[6] = ⟨64, base + 48⟩ ∧ b[7] = ⟨64, dst⟩ ∧ b[22] = ⟨1, 0⟩ := by
    refine ⟨?_, ?run, ?_⟩
    case run =>
      cfg_eval [h4, h3, h14, ok]
      rfl
    exact ⟨rfl, rfl, rfl, df⟩
  obtain ⟨b, call, b4, b6, b7, b22⟩ := call
  have rsrc : Readable m (base + 48) 40 := win.readable.of_offsets rfl (addr_sub base 121) (by decide)
  have input : WordsAt pushed (base + 48) 64 w :=
    words.write_apart _ _ (RangeApart.of_offsets (addr_sub base 8) rfl (by decide))
  obtain ⟨lower, off, offset⟩ := Sec1.Serialize.Coordinates.stackOffsets win.readable.low
  obtain ⟨o, ex, tag, pop, _, keep, frame, result⟩ := Sec1.Serialize.packExecution
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l1148d0 x hx))
    b4 b6 b7 (rsrc.memStore _ _) (dest.memStore _ _) input (slot.readable.memStore _ _)
    (show memLoad pushed (base - 8) 64 = 0x1203a3 from memLoad_memStore_same _ _ _ (by decide) (by decide))
    (by decide) (Or.inl (by omega))
  have run := Ecdh.Transfer.sec1Exec (dst := .l1148d0) (by decide) rfl ex
  have sp' : o.values[4] = ⟨64, base⟩ := by simpa only [BitVec.sub_add_cancel] using pop
  have hsp : o.values[4].get 64 = base := by rw [sp']; rfl
  have df' : o.values[22] = ⟨1, 0⟩ := (keep 22 (by decide)).trans b22
  have pushedFrame : RamWriteFrame m pushed [⟨(base - 8).toNat, 8⟩, ⟨dst.toNat, 32⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _, ?_⟩
    have h := slot.readable.low
    change (base - 8).toNat + 8 ≤ 2^64
    omega
  have frame' := pushedFrame.trans frame (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
  have low := win.readable.low
  have outside (i : Nat) (h : i ≤ 104) :
      Outside [⟨(base - 8).toNat, 8⟩, ⟨dst.toNat, 32⟩] (base + BitVec.ofNat 64 i) 8 := by
    have addr := offset i (by omega)
    have := dest.readable.low
    refine ⟨by omega, ?_⟩
    intro r hr; rcases List.mem_cons.mp hr with rfl | ht
    · right; change (base - 8).toNat + 8 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp ht
      left; change _ + 8 ≤ dst.toNat; omega
  have saved' : memLoad o.store (base + 88) 64 = bx :=
    (frame'.memLoad_eq (outside 88 (by decide))).trans saved
  have ret' : memLoad o.store (base + 104) 64 = 0x101b1d :=
    (frame'.memLoad_eq (outside 104 (by decide))).trans ret
  have load (i : Nat) (hi : i ≤ 104) : LoadOk o.store (base + BitVec.ofNat 64 i) 8 := by
    apply LoadOk.of_region (win.readable.of_frame frame')
    all_goals have := offset i (by omega); omega
  have l88 : LoadOk o.store (base + 88) 8 := load 88 (by decide)
  have l96 : LoadOk o.store (base + 96) 8 := load 96 (by decide)
  have l104 : LoadOk o.store (base + 104) 8 := load 104 (by decide)
  have add88 : (addSpec base (88 : Word)).1 = base + 88 := rfl
  have tail : ∃ u, program.runBlock (dialect Extracted.programImage) ⟨.l1203a3, o.values, o.store⟩ =
      .returned u ∧ u.tag = some ⟨64, 0x101b1d⟩ ∧ u.values[4] = ⟨64, base + 112⟩ ∧
      u.values[3] = ⟨64, bx⟩ ∧ u.values[22] = ⟨1, 0⟩ ∧ u.store = o.store := by
    refine ⟨?_, ?run, ?_⟩
    case run =>
      cfg_eval [hsp, add88, BitVec.add_assoc, l88, l96, l104, ret', saved']
      rfl
    exact ⟨rfl, rfl, rfl, df', rfl⟩
  obtain ⟨u, tail, ut, us, ub, ud, um⟩ := tail
  refine ⟨u, ParseSignature.exec_call call run (by rw [tag]; rfl) (.done ?_), ut, us, ub, ud, um ▸ frame', um ▸ result⟩
  change program.step _ ⟨⟨.l1203a3, o.values, o.store⟩, []⟩ = .done u
  simp only [Program.step, tail, CFG.Transfer.next]

end K256.Proofs.Ecdh.Output
