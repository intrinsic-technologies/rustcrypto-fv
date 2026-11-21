import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey.Memory
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

theorem keyCallFrame {fr : Activation} {input : Input} {state : State}
    {a b : Verify.Core.Registers} {m n : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (keyAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (writes : RamWriteFrame m n (keyWrites fr))
    (keep : ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i])
    (bx : b[3].width = 64) (bytes : StateAt n fr.rdi ⟨nextKey second input state, state.value⟩) :
    Live (keyAt second input) fr (b.set 4 ⟨64, sp fr⟩) n ⟨nextKey second input state, state.value⟩ ∧
      (seeded input = true → Slots fr n) := by
  have depth := env.depth
  have limit := env.limit
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have push : sp fr - 8 = fr.rsp - 720 := by unfold sp; bv_omega
  have offset (d : BitVec 64) (hd : d.toNat ≤ 1920) :
      (fr.rsp - d).toNat = fr.rsp.toNat - d.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have pushNat : (sp fr - 8).toNat = fr.rsp.toNat - 720 := by
    rw [push, offset _ (by decide)]
    rfl
  have total := live.writes.trans writes (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩ <;>
        simp only [Activation.region, pushNat, bottom] <;> omega
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        Nat.le_refl _, by change fr.rdi.toNat + 32 ≤ fr.rdi.toNat + 64; omega⟩)
  have outsideStack (d : BitVec 64) (hd : d.toNat ≤ 712) :
      Outside (keyWrites fr) (fr.rsp - d) 8 := by
    have addr := offset d (by omega)
    refine ⟨by rw [addr]; change _ + 8 ≤ 2^64; omega, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · right
      change (sp fr - 8).toNat + 8 ≤ (fr.rsp - d).toNat
      omega
    · obtain rfl := List.mem_singleton.mp hr
      change (fr.rsp - d).toNat + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ (fr.rsp - d).toNat
      rcases env.apart with h | h <;> omega
  have load (d : BitVec 64) (hd : d.toNat ≤ 712) :
      memLoad n (fr.rsp - d) 64 = memLoad m (fr.rsp - d) 64 :=
    writes.memLoad_eq (outsideStack d hd)
  have ret := load 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at ret
  have stateSlot : memLoad n (fr.rsp - 592) 64 = memLoad m (fr.rsp - 592) 64 :=
    load 592 (by decide)
  have slotsAfter (hs : seeded input = true) : Slots fr n := by
    apply Absorb.slotsAfter (slots hs) writes
    · rw [show sp fr + 8 = fr.rsp - 704 by unfold sp; bv_omega]
      exact outsideStack 704 (by decide)
    · rw [show sp fr + 112 = fr.rsp - 600 by unfold sp; bv_omega]
      exact outsideStack 600 (by decide)
    · rw [show sp fr + 120 = fr.rsp - 592 by unfold sp; bv_omega]
      exact outsideStack 592 (by decide)
  let restored := b.set 4 ⟨64, sp fr⟩
  have rsp : restored[4] = ⟨64, sp fr⟩ := by
    simp only [restored, Vector.getElem_set, ↓reduceIte]
  have reg (i : Fin Reg.count) (ne : i.val ≠ 4) : restored[i] = b[i] := by
    simp only [restored, Fin.getElem_fin, Vector.getElem_set, Ne.symm ne, ↓reduceIte]
  have same (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,14,15,22,39,50,51]) :
      restored[i] = a[i] :=
    (reg i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)).trans (keep i hi)
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      restored[i].width = 64 := by
    by_cases h : i.val = 3
    · obtain rfl : i = 3 := Fin.ext h
      rw [reg 3 (by decide)]
      exact bx
    · rw [same i (by simp only [Activation.calleeSavedNumbers, List.mem_cons,
        List.not_mem_nil, or_false] at hi ⊢; omega)]
      exact live.savedWidths i hi
  have tables := Fn103f30.callSlots_loaded (sections := Extracted.programSections)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (env.imageAt total)
  obtain ⟨copyRead, copyWord⟩ := tables (0x203dd0, 0x12a820) (by decide)
  obtain ⟨fillRead, fillWord⟩ := tables (0x203e10, 0x12a700) (by decide)
  have tailAfter (old : Absorb.FrameTail fr a m) : Absorb.FrameTail fr restored n := by
    obtain ⟨sb, s12, s13, s14, s15, s5, rd, rt, rtLow, win, room, align, _, _, _, _, gap, _⟩ := old
    exact ⟨(load 48 (by decide)).trans sb, (load 40 (by decide)).trans s12,
      (load 32 (by decide)).trans s13, (load 24 (by decide)).trans s14,
      (load 16 (by decide)).trans s15, (load 8 (by decide)).trans s5,
      Readable.of_frame rd writes, ret.trans rt, rtLow, Writable.of_frame win writes,
      room, align, copyRead, copyWord, fillRead, fillWord, gap, trivial⟩
  refine ⟨⟨?_, total, bytes, ?_, widths⟩, slotsAfter⟩
  · have old := live.atoms
    cases second
    · cases input
      · obtain ⟨_, df, bp, r14, r15, mx, ft, fc, tail⟩ := old
        exact ⟨rsp, (same 22 (by decide)).trans df, (same 5 (by decide)).trans bp,
          (same 14 (by decide)).trans r14, (same 15 (by decide)).trans r15,
          (same 39 (by decide)).trans mx, (same 50 (by decide)).trans ft,
          (same 51 (by decide)).trans fc, tailAfter tail⟩
      · obtain ⟨_, df, r14, mx, ft, fc, slot, tail⟩ := old
        exact ⟨rsp, (same 22 (by decide)).trans df, (same 14 (by decide)).trans r14,
          (same 39 (by decide)).trans mx, (same 50 (by decide)).trans ft,
          (same 51 (by decide)).trans fc, stateSlot.trans slot, tailAfter tail⟩
    · obtain ⟨_, df, mx, ft, fc, tail⟩ := old
      exact ⟨rsp, (same 22 (by decide)).trans df, (same 39 (by decide)).trans mx,
        (same 50 (by decide)).trans ft, (same 51 (by decide)).trans fc, tailAfter tail⟩
  · cases second <;> cases input <;> intro h <;> cases h

end K256.Proofs.Signing.Nonce.Initialize.Update
