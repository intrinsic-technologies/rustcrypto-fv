import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem spOffset {fr : Activation} {input : Input} (env : Environment fr input)
    (off : BitVec 64) (fit : off.toNat ≤ 712) :
    (sp fr + off).toNat = fr.rsp.toNat - 712 + off.toNat := by
  have dep := env.depth
  have lt := env.limit
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from by
    change 712 ≤ fr.rsp.toNat; omega)]
  change (_ - 712 + off.toNat) % 2^64 = _
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem padBounds {fr : Activation} {input : Input} (env : Environment fr input)
    (second : Bool) :
    fr.rsp.toNat - 712 + 48 ≤ (pad fr second).toNat ∧
      (pad fr second).toNat + 64 ≤ fr.rsp.toNat - 712 + 224 := by
  cases second <;> simp only [pad, Bool.false_eq_true, ↓reduceIte,
    spOffset env _ (by decide : (48 : BitVec 64).toNat ≤ 712),
    spOffset env _ (by decide : (160 : BitVec 64).toNat ≤ 712), BitVec.reduceToNat] <;> omega

private theorem padWithin {fr : Activation} {input : Input} (env : Environment fr input)
    (second : Bool) :
    RegionsWithin [⟨(pad fr second).toNat, 64⟩] [fr.region] := by
  have dep := env.depth
  have low : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have bounds := padBounds env second
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_, List.mem_cons_self, ?_, ?_⟩
  · change fr.low.toNat ≤ (pad fr second).toNat; omega
  · change (pad fr second).toNat + 64 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    omega

theorem padWritable {fr : Activation} {input : Input} {m : Ram}
    (env : Environment fr input) (second : Bool)
    (writes : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,64⟩]) :
    Writable Extracted.programImage m (pad fr second) 64 := by
  have dep := env.depth
  have lo : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)
  have bounds := padBounds env second
  exact (env.stack.of_frame writes).sub (by omega) (by omega)

private theorem outsidePad {fr : Activation} {second : Bool} {addr : BitVec 64} {len : Nat}
    (bound : addr.toNat + len ≤ 2^64)
    (apart : addr.toNat + len ≤ (pad fr second).toNat ∨ (pad fr second).toNat + 64 ≤ addr.toNat) :
    Outside [⟨(pad fr second).toNat,64⟩] addr len := by
  refine ⟨bound, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  exact apart

private theorem frameAtoms {fr : Activation} {input : Input} {a b : Verify.Core.Registers}
    {m n : Ram} (env : Environment fr input) (second outer : Bool)
    (entry : Atom.All Extracted.programImage a m (Fn103f30.frameAt (head second outer) fr))
    (writes : RamWriteFrame m n [⟨(pad fr second).toNat,64⟩])
    (keep : ∀ i : Fin Reg.count, i.val ≠ 0 → i.val ≠ 19 → b[i] = a[i]) :
    Atom.All Extracted.programImage b n (Fn103f30.frameAt (exitLabel second outer) fr) := by
  have dep := env.depth
  have lim := env.limit
  have bounds := padBounds env second
  have ret := writes.memLoad_eq (k := 64) (outsidePad (addr := fr.rsp) (by change _ + 8 ≤ _; omega)
    (.inr (by omega)))
  have saved (off : BitVec 64) (h : off.toNat ≤ 48) :
      memLoad n (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    have addr := BitVec.toNat_sub_of_le (show off ≤ fr.rsp from by change off.toNat ≤ _; omega)
    exact writes.memLoad_eq (outsidePad (by change _ + 8 ≤ _; omega) (.inr (by omega)))
  have sep : 0x204598 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 := by
    cases second <;> cases outer <;>
      simp only [head, Bool.false_eq_true, ↓reduceIte, Fn103f30.frameAt, Fn103f30.frameAtG4,
        Atom.All, Atom.Holds, Atom.gpr] at entry <;> grind only
  have call₁ := writes.memLoad_eq (k := 64) (outsidePad (addr := 0x203dd0) (by decide)
    (by change 0x203dd0 + 8 ≤ _ ∨ _ ≤ 0x203dd0; omega))
  have call₂ := writes.memLoad_eq (k := 64) (outsidePad (addr := 0x203e10) (by decide)
    (by change 0x203e10 + 8 ≤ _ ∨ _ ≤ 0x203e10; omega))
  cases second <;> cases outer <;>
    simp only [head, exitLabel, Bool.false_eq_true, ↓reduceIte, Fn103f30.frameAt, Fn103f30.frameAtG4,
      Atom.All, Atom.Holds, Atom.gpr] at entry ⊢
  all_goals
    simp only [keep 3 (by decide) (by decide), keep 4 (by decide) (by decide),
      keep 5 (by decide) (by decide), keep 7 (by decide) (by decide), keep 8 (by decide) (by decide),
      keep 9 (by decide) (by decide), keep 12 (by decide) (by decide), keep 13 (by decide) (by decide),
      keep 14 (by decide) (by decide), keep 15 (by decide) (by decide), keep 22 (by decide) (by decide),
      keep 39 (by decide) (by decide), keep 50 (by decide) (by decide), keep 51 (by decide) (by decide),
      ret, call₁, call₂, saved 48 (by decide), saved 40 (by decide), saved 32 (by decide),
      saved 24 (by decide), saved 16 (by decide), saved 8 (by decide)]
    have st : Writable Extracted.programImage n (fr.rsp - 1920) 1920 := Writable.of_frame (by grind only) writes
    have rd : Readable n fr.rsp 8 := Readable.of_frame (by grind only) writes
    have rd₁ : Readable n 0x203dd0 8 := Readable.of_frame (by grind only) writes
    have rd₂ : Readable n 0x203e10 8 := Readable.of_frame (by grind only) writes
    grind only

theorem loopPost {fr : Activation} {input : Input} {a b : Verify.Core.Registers} {m n : Ram}
    {state : State} (env : Environment fr input) (second outer : Bool)
    (live : Live (head second outer) fr a m state) (slots : second = true → Slots fr m)
    (hash : outer = true → Compressed fr second m state.key)
    (writes : RamWriteFrame m n [⟨(pad fr second).toNat,64⟩])
    (keep : ∀ i : Fin Reg.count, i.val ≠ 0 → i.val ≠ 19 → b[i] = a[i]) :
    Live (exitLabel second outer) fr b n state ∧ (second = true → Slots fr n) ∧
      (outer = true → Compressed fr second n state.key) := by
  have within := padWithin env second
  have stackWrites := (RamWriteFrame.refl m [fr.region]).trans writes within
  have dep := env.depth
  have lim := env.limit
  have bounds := padBounds env second
  refine ⟨⟨frameAtoms env second outer live.atoms writes keep, live.writes.trans writes ?_,
    env.stateAfter live.bytes stackWrites, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, h⟩ := within r hr
    obtain rfl := List.mem_singleton.mp hs
    exact ⟨_, List.mem_cons_self, h⟩
  · cases second <;> cases outer <;> intro h <;> cases h
  · intro i hi
    have : i.val ≠ 0 ∧ i.val ≠ 19 := by
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    rw [keep i this.1 this.2]
    exact live.savedWidths i hi
  · intro h
    subst second
    have padEq : (pad fr true).toNat = fr.rsp.toNat - 712 + 48 := spOffset env 48 (by decide)
    have slot (off : BitVec 64) (lo : off.toNat + 8 ≤ 48 ∨ 112 ≤ off.toNat) (hi : off.toNat ≤ 712) :
        memLoad n (sp fr + off) 64 = memLoad m (sp fr + off) 64 := by
      have := spOffset env off hi
      exact writes.memLoad_eq (outsidePad (by change _ + 8 ≤ _; omega) (by change _ + 8 ≤ _ ∨ _; omega))
    exact ⟨(slot 8 (by decide) (by decide)).trans (slots rfl).stop,
      (slot 112 (by decide) (by decide)).trans (slots rfl).value,
      (slot 120 (by decide) (by decide)).trans (slots rfl).state⟩
  · intro h
    have out (off : BitVec 64) (len : Nat) (lo : 224 ≤ off.toNat) (hi : off.toNat + len ≤ 712) :
        Outside [⟨(pad fr second).toNat,64⟩] (sp fr + off) len := by
      have := spOffset env off (by omega)
      exact outsidePad (by omega) (.inr (by omega))
    exact ⟨(writes.memLoad_eq (out 391 1 (by decide) (by decide))).trans (hash h).used,
      UpdateV.Finalize.stateAfter writes (out 392 32 (by decide) (by decide)) (hash h).hash,
      (writes.memLoad_eq (out 424 8 (by decide) (by decide))).trans (hash h).count⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
