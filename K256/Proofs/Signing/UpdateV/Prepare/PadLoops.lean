import K256.Proofs.Signing.UpdateV.State
import K256.Proofs.Verify.LIR.Fn104970
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2 K256.Proofs.Verify.Hash

abbrev padAddr (sp : BitVec 64) (i : Nat) : BitVec 64 :=
  sp + 8 + BitVec.ofNat 64 i

def xorPadByte (sp : BitVec 64) (mask : BitVec 8) (m : Ram) (i : Nat) : Ram :=
  memStore m (padAddr sp i) (memLoad m (padAddr sp i) 8 ^^^ mask)

def xorPadFour (sp : BitVec 64) (mask : BitVec 8) (m : Ram) (i : Nat) : Ram :=
  let m₁ := xorPadByte sp mask m i
  let m₂ := xorPadByte sp mask m₁ (i + 1)
  let m₃ := xorPadByte sp mask m₂ (i + 2)
  xorPadByte sp mask m₃ (i + 3)

private abbrev padHead (outer : Bool) : Label := if outer then .l104ab0 else .l104a00
private abbrev padExit (outer : Bool) : Label := if outer then .l104ace else .l104a1e
private abbrev padCode (outer : Bool) : List UInt8 := if outer then bytes_l104ab0 else bytes_l104a00
private abbrev padPC (outer : Bool) : BitVec 64 := if outer then 0x104ab0 else 0x104a00
abbrev padMask (outer : Bool) : BitVec 8 := if outer then 0x6a else 0x36

private theorem padAddr_toNat {sp : BitVec 64} (bound : (sp + 8).toNat + 64 ≤ 2^32)
    {i : Nat} (hi : i < 64) : (padAddr sp i).toNat = (sp + 8).toNat + i := by
  change (sp + 8 + BitVec.ofNat 64 i).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 600000 in
private theorem xorPadStep (outer : Bool) {sp : BitVec 64} {a : Values Value Reg.count}
    {m : Ram} {j : Nat} (hj : j < 16) (rsp : a[4] = ⟨64, sp⟩)
    (index : a[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * j)⟩)
    (wr : Writable Extracted.programImage m (sp + 8) 64) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨padHead outer, a, m⟩ =
        .jump ⟨if j + 1 = 16 then padExit outer else padHead outer,
          b, xorPadFour sp (padMask outer) m (4 * j)⟩ ∧
      b[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * (j + 1))⟩ ∧
      (∀ i : Fin Reg.count, i.val ≠ 0 → i.val ≠ 19 → b[i] = a[i]) := by
  let mask := padMask outer
  let m₁ := xorPadByte sp mask m (4 * j)
  let m₂ := xorPadByte sp mask m₁ (4 * j + 1)
  let m₃ := xorPadByte sp mask m₂ (4 * j + 2)
  have code : ∀ x ∈ codeRange (padPC outer) (padCode outer), x ∈ Extracted.programImage := by
    cases outer
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l104a00 x hx)
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l104ab0 x hx)
  have size : (padCode outer).length = 30 := by cases outer <;> rfl
  have guard {t : Ram} (w : Writable Extracted.programImage t (sp + 8) 64)
      (k : Nat) (hk : k < 4) :
      StoreOk Extracted.programImage t (padAddr sp (4 * j + k)) 1
        (padPC outer + BitVec.ofNat 64 (5 * k)) 5 := by
    have addr := padAddr_toNat w.readable.low (i := 4 * j + k) (by omega)
    exact ParseSignature.storeOk_of_codeRange (w.sub (by rw [addr]; omega) (by rw [addr]; omega))
      code (by rw [size]; omega)
  have g₀ := guard wr 0 (by decide)
  have w₁ : Writable Extracted.programImage m₁ (sp + 8) 64 := wr.memStore _ _
  have g₁ := guard w₁ 1 (by decide)
  have w₂ : Writable Extracted.programImage m₂ (sp + 8) 64 := w₁.memStore _ _
  have g₂ := guard w₂ 2 (by decide)
  have w₃ : Writable Extracted.programImage m₃ (sp + 8) 64 := w₂.memStore _ _
  have g₃ := guard w₃ 3 (by decide)
  have spBits : a[4].get 64 = sp := congrArg (Value.get 64) rsp
  have indexBits : a[0].get 64 = BitVec.ofNat 64 (3 + 4 * j) :=
    congrArg (Value.get 64) index
  have incr : BitVec.ofNat 64 (3 + 4 * j) + 4 =
      BitVec.ofNat 64 (3 + 4 * (j + 1)) := by
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add, show 3 + 4 * j + 4 = 3 + 4 * (j + 1) by omega]
  have addr (k : Nat) :
      sp + BitVec.ofNat 64 (3 + 4 * j) + BitVec.ofNat 64 (5 + k) = padAddr sp (4 * j + k) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 3 + 4 * j + (5 + k) = 8 + (4 * j + k) by omega,
      BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  have addr0 : sp + BitVec.ofNat 64 (3 + 4 * j) + 5 = padAddr sp (4 * j + 0) := addr 0
  have addr1 : sp + BitVec.ofNat 64 (3 + 4 * j) + 6 = padAddr sp (4 * j + 1) := addr 1
  have addr2 : sp + BitVec.ofNat 64 (3 + 4 * j) + 7 = padAddr sp (4 * j + 2) := addr 2
  have addr3 : sp + BitVec.ofNat 64 (3 + 4 * j) + 8 = padAddr sp (4 * j + 3) := addr 3
  have done : (BitVec.ofNat 64 (3 + 4 * (j + 1)) == 0x43) = decide (j + 1 = 16) := by
    change decide (_ = (0x43 : BitVec 64)) = _
    rw [decide_eq_decide]
    constructor
    · intro h
      have eq := congrArg BitVec.toNat h
      change (3 + 4 * (j + 1)) % 2^64 = 67 at eq
      rw [Nat.mod_eq_of_lt (by omega)] at eq
      omega
    · intro h
      rw [h]
      rfl
  let b := (a.set 0 ⟨64, BitVec.ofNat 64 (3 + 4 * (j + 1))⟩).set 19
    (.ofBool (decide (j + 1 = 16)))
  refine ⟨b, ?_, ?_, ?_⟩
  · cases outer <;>
      first
      | change program.runBlock _ ⟨.l104a00, a, m⟩ = _
      | change program.runBlock _ ⟨.l104ab0, a, m⟩ = _
    all_goals
      cfg_eval [spBits, indexBits]
      rw [addr0, addr1, addr2, addr3]
      split <;> try (rename_i ng; exact (ng g₀).elim)
      split <;> try (rename_i ng; exact (ng g₁).elim)
      split <;> try (rename_i ng; exact (ng g₂).elim)
      split <;> try (rename_i ng; exact (ng g₃).elim)
      rw [incr, cmpSpec_ZF, done]
      by_cases finish : j + 1 = 16
      all_goals
        simp only [finish, decide_true, decide_false, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ↓reduceIte]
        congr 2
        all_goals
          first
          | solve | simp only [finish, ↓reduceIte, padHead, padExit] <;> rfl
          | apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
              fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
            intro i
            finite_cases i <;> simp only [b, Vector.getElem_set, finish] <;> rfl
  · simp only [b, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  · intro i h₀ h₁₉
    simp only [b, Fin.getElem_fin, Vector.getElem_set, ite_eq_right (Ne.symm h₀), ite_eq_right (Ne.symm h₁₉)]

abbrev padBefore (outer : Bool) : UInt8 := if outer then 0x36 else 0
abbrev padAfter (outer : Bool) : UInt8 := if outer then 0x5c else 0x36

private def PadPrefix (sp : BitVec 64) (outer : Bool) (key : ByteArray) (m : Ram)
    (n : Nat) : Prop :=
  ∀ i < 64, m[padAddr sp i]? =
    some (key.data[i]?.getD 0 ^^^ (if i < n then padAfter outer else padBefore outer))

private theorem xorPadByte_prefix {sp : BitVec 64} {outer : Bool} {key : ByteArray}
    {m : Ram} {n : Nat} (hn : n < 64) (prefixBytes : PadPrefix sp outer key m n) :
    PadPrefix sp outer key (xorPadByte sp (padMask outer) m n) (n + 1) := by
  intro i hi
  by_cases eq : i = n
  · subst i
    have hn' := prefixBytes n hn
    rw [ite_eq_right (Nat.lt_irrefl n)] at hn'
    rw [ite_eq_left (Nat.lt_succ_self n), xorPadByte]
    have store := memStore_getElem?_self m (padAddr sp n)
      (memLoad m (padAddr sp n) 8 ^^^ padMask outer) (by decide) 0 (by decide)
    rw [show padAddr sp n + BitVec.ofNat 64 0 = padAddr sp n from BitVec.add_zero _] at store
    rw [store, memLoad_8, memByte]
    change some (storedByte ((m[padAddr sp n]?.getD 0).toBitVec ^^^ padMask outer) 0) = _
    rw [hn', Option.getD_some]
    congr 1
    have mask : (padBefore outer).toBitVec ^^^ padMask outer = (padAfter outer).toBitVec := by
      cases outer <;> rfl
    rw [UInt8.toBitVec_xor, BitVec.xor_assoc, mask, ← UInt8.toBitVec_xor]
    change UInt8.ofNat _ = _
    change UInt8.ofNat (key.data[n]?.getD 0 ^^^ padAfter outer).toNat = _
    exact UInt8.ofNat_toNat
  · rw [xorPadByte, memStore_getElem?_of_ne]
    · simp only [prefixBytes i hi, show (i < n + 1) ↔ i < n by omega]
    · intro k hk
      have zero : k = 0 := by omega
      subst k
      rw [show padAddr sp n + BitVec.ofNat 64 0 = padAddr sp n from BitVec.add_zero _]
      intro h
      exact eq (add_ofNat_inj (sp + 8) (by omega) (by omega) h).symm

private theorem xorPadFour_prefix {sp : BitVec 64} {outer : Bool} {key : ByteArray}
    {m : Ram} {i : Nat} (hi : i + 4 ≤ 64) (p : PadPrefix sp outer key m i) :
    PadPrefix sp outer key (xorPadFour sp (padMask outer) m i) (i + 4) := by
  exact xorPadByte_prefix (by omega) (xorPadByte_prefix (by omega)
    (xorPadByte_prefix (by omega) (xorPadByte_prefix (by omega) p)))

private theorem xorPadFour_frame {sp : BitVec 64} {mask : BitVec 8} {base m : Ram} {i : Nat}
    (bound : (sp + 8).toNat + 64 ≤ 2^32) (hi : i + 4 ≤ 64)
    (frame : RamWriteFrame base m [⟨(sp + 8).toNat, 64⟩]) :
    RamWriteFrame base (xorPadFour sp mask m i) [⟨(sp + 8).toNat, 64⟩] := by
  have within (k : Nat) (hk : k < 64) : InRegions [⟨(sp + 8).toNat, 64⟩] (padAddr sp k) 1 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    unfold InRegion
    rw [padAddr_toNat bound hk]
    change (sp + 8).toNat ≤ (sp + 8).toNat + k ∧
      (sp + 8).toNat + k + 1 ≤ (sp + 8).toNat + 64 ∧ (sp + 8).toNat + k + 1 ≤ 2^64
    omega
  exact (((frame.memStore _ (within i (by omega))).memStore _ (within (i + 1) (by omega))).memStore
    _ (within (i + 2) (by omega))).memStore _ (within (i + 3) (by omega))

theorem runPadLoop (outer : Bool) (head exit : Label) (preserved : Fin Reg.count → Prop)
    (keepRsp : preserved 4) {sp rsp : BitVec 64} {a : Values Value Reg.count} {m : Ram}
    {key : ByteArray} (rspEq : a[4] = ⟨64, rsp⟩) (index : a[0] = ⟨64, 3⟩)
    (writable : Writable Extracted.programImage m (sp + 8) 64)
    (bytes : (⟨(sp + 8).toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key (padBefore outer)))
    (step : ∀ {a' : Values Value Reg.count} {m' : Ram} {j : Nat},
      j < 16 → a'[4] = ⟨64, rsp⟩ → a'[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * j)⟩ →
      Writable Extracted.programImage m' (sp + 8) 64 →
      ∃ b, program.runBlock (dialect Extracted.programImage) ⟨head, a', m'⟩ =
          .jump ⟨if j + 1 = 16 then exit else head, b, xorPadFour sp (padMask outer) m' (4 * j)⟩ ∧
        b[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * (j + 1))⟩ ∧
        (∀ i : Fin Reg.count, preserved i → b[i] = a'[i])) :
    ∃ (b : Values Value Reg.count) (t : Ram),
      (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨head, a, m⟩, []⟩ ⟨⟨exit, b, t⟩, []⟩ ∧
      RamWriteFrame m t [⟨(sp + 8).toNat, 64⟩] ∧
      (∀ i : Fin Reg.count, preserved i → b[i] = a[i]) ∧
      (⟨(sp + 8).toNat, 64⟩ : MemoryRegion).HasBytes t (keyPad key (padAfter outer)) := by
  let padRegion : MemoryRegion := ⟨(sp + 8).toNat, 64⟩
  have bound := writable.readable.low
  have atByte (i : Nat) (hi : i < 64) :
      BitVec.ofNat 64 ((sp + 8).toNat + i) = padAddr sp i := by
    rw [← padAddr_toNat bound hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have p0 : PadPrefix sp outer key m 0 := by
    intro i hi
    have hlen : i < (keyPad key (padBefore outer)).size := by rwa [keyPad_size]
    have h := bytes.2 ⟨i, hlen⟩
    change m[BitVec.ofNat 64 ((sp + 8).toNat + i)]? =
      some ((keyPad key (padBefore outer))[i]'hlen) at h
    rw [atByte i hi, keyPad_getElem key (padBefore outer) i hi] at h
    exact h
  have journey (j : Nat) (hj : j ≤ 16) :
      ∃ (b : Values Value Reg.count) (t : Ram),
        (program.sem (dialect Extracted.programImage)).Reaches
          ⟨⟨head, a, m⟩, []⟩
          ⟨⟨if j = 16 then exit else head, b, t⟩, []⟩ ∧
        b[0] = ⟨64, BitVec.ofNat 64 (3 + 4 * j)⟩ ∧
        (∀ i : Fin Reg.count, preserved i → b[i] = a[i]) ∧
        RamWriteFrame m t [padRegion] ∧ PadPrefix sp outer key t (4 * j) := by
    induction j with
    | zero =>
      exact ⟨a, m, .refl _, index, fun _ _ => rfl, .refl _ _, p0⟩
    | succ j ih =>
      have notDone : j ≠ 16 := by omega
      obtain ⟨b, t, reach, counter, keep, wr, pref⟩ := ih (by omega)
      rw [ite_eq_right notDone] at reach
      obtain ⟨c, run, counter', keep'⟩ :=
        step (by omega) ((keep 4 keepRsp).trans rspEq) counter (writable.of_frame wr)
      refine ⟨c, _, reach.trans (Semantics.Reaches.single (congrArg (Transfer.next _ []) run)),
        counter', fun i hi => (keep' i hi).trans (keep i hi),
        xorPadFour_frame bound (by omega) wr, ?_⟩
      rw [show 4 * (j + 1) = 4 * j + 4 by omega]
      exact xorPadFour_prefix (by omega) pref
  obtain ⟨b, t, reach, _, keep, writes, pref⟩ := journey 16 (by decide)
  refine ⟨b, t, reach, writes, keep, keyPad_size _ _, ?_⟩
  intro i
  have hi : i.val < 64 := by simpa only [keyPad_size] using i.isLt
  change t[BitVec.ofNat 64 ((sp + 8).toNat + i.val)]? =
    some ((keyPad key (padAfter outer))[i.val]'i.isLt)
  rw [atByte i.val hi, keyPad_getElem key (padAfter outer) i.val hi]
  simpa only [ite_eq_left hi] using pref i.val hi

local macro "unfold_pad_entry" h:ident fr:ident : tactic =>
  `(tactic| (
    first
    | change Atom.All _ _ _ (Fn104970.frameAt .l104a00 $fr) at $h:ident
    | change Atom.All _ _ _ (Fn104970.frameAt .l104ab0 $fr) at $h:ident
    simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds, Atom.gpr] at $h:ident))

private theorem padStart_toNat {rsp : BitVec 64}
    (depth : 1200 ≤ rsp.toNat) (limit : rsp.toNat + 8 < 2^32) :
    (rsp - 488 + 8).toNat = rsp.toNat - 480 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (show (488 : BitVec 64) ≤ rsp from by
      change 488 ≤ rsp.toNat
      omega)]
    change (rsp.toNat - 488 + 8) % 2^64 = rsp.toNat - 480
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

private theorem padFrame {fr : Activation} {a b : Values Value Reg.count} {m t : Ram}
    (outer : Bool) (depth : 1200 ≤ fr.rsp.toNat) (limit : fr.rsp.toNat + 8 < 2^32)
    (entry : Atom.All Extracted.programImage a m (Fn104970.frameAt (padHead outer) fr))
    (keep : ∀ i : Fin Reg.count, i.val ≠ 0 → i.val ≠ 19 → b[i] = a[i])
    (frame : RamWriteFrame m t [⟨(fr.rsp - 488 + 8).toNat, 64⟩]) :
    Atom.All Extracted.programImage b t (Fn104970.frameAt (padExit outer) fr) := by
  have padStart := padStart_toNat depth limit
  have sameWord {addr : BitVec 64} (bound : addr.toNat + 8 ≤ 2^64)
      (apart : addr.toNat + 8 ≤ fr.rsp.toNat - 480 ∨ fr.rsp.toNat - 480 + 64 ≤ addr.toNat) :
      memLoad t addr 64 = memLoad m addr 64 := by
    apply frame.memLoad_eq
    refine ⟨bound, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [padStart] at ⊢
    exact apart
  have sameSave (off : Nat) (h : off ≤ 48) : memLoad t (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
    have offNat : (BitVec.ofNat 64 off).toNat = off := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have addr : (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
      rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 off).toNat ≤ fr.rsp.toNat; omega), offNat]
    exact sameWord (by omega) (.inr (by omega))
  have save48 : memLoad t (fr.rsp - 48) 64 = memLoad m (fr.rsp - 48) 64 :=
    sameSave 48 (by decide)
  have save40 : memLoad t (fr.rsp - 40) 64 = memLoad m (fr.rsp - 40) 64 :=
    sameSave 40 (by decide)
  have save32 : memLoad t (fr.rsp - 32) 64 = memLoad m (fr.rsp - 32) 64 :=
    sameSave 32 (by decide)
  have save24 : memLoad t (fr.rsp - 24) 64 = memLoad m (fr.rsp - 24) 64 :=
    sameSave 24 (by decide)
  have save16 : memLoad t (fr.rsp - 16) 64 = memLoad m (fr.rsp - 16) 64 :=
    sameSave 16 (by decide)
  have save8 : memLoad t (fr.rsp - 8) 64 = memLoad m (fr.rsp - 8) 64 :=
    sameSave 8 (by decide)
  have separation : 0x2042c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 := by
    cases outer <;> unfold_pad_entry entry fr <;> grind only
  have call₁ : memLoad t 0x203dd0 64 = memLoad m 0x203dd0 64 := sameWord (by decide) (by
    change 0x203dd0 + 8 ≤ fr.rsp.toNat - 480 ∨ fr.rsp.toNat - 480 + 64 ≤ 0x203dd0
    omega)
  have call₂ : memLoad t 0x203e10 64 = memLoad m 0x203e10 64 := sameWord (by decide) (by
    change 0x203e10 + 8 ≤ fr.rsp.toNat - 480 ∨ fr.rsp.toNat - 480 + 64 ≤ 0x203e10
    omega)
  have retWord : memLoad t fr.rsp 64 = memLoad m fr.rsp 64 := sameWord (by omega) (.inr (by omega))
  have frames : Fn104970.frameAt (padHead outer) fr = Fn104970.frameAt (padExit outer) fr := by
    cases outer <;> rfl
  rw [← frames]
  cases outer <;> unfold_pad_entry entry fr
  all_goals
    first
    | change Atom.All _ _ _ (Fn104970.frameAt .l104a00 fr)
    | change Atom.All _ _ _ (Fn104970.frameAt .l104ab0 fr)
    simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds, Atom.gpr]
  all_goals
    simp only [keep 3 (by decide) (by decide), keep 4 (by decide) (by decide),
      keep 5 (by decide) (by decide), keep 7 (by decide) (by decide), keep 8 (by decide) (by decide),
      keep 9 (by decide) (by decide), keep 12 (by decide) (by decide), keep 13 (by decide) (by decide),
      keep 14 (by decide) (by decide), keep 15 (by decide) (by decide), keep 22 (by decide) (by decide),
      keep 39 (by decide) (by decide), keep 50 (by decide) (by decide), keep 51 (by decide) (by decide),
      retWord, call₁, call₂, save48, save40, save32, save24, save16, save8]
    have stack : Writable Extracted.programImage t (fr.rsp - 0x4b0) 0x4b0 :=
      Writable.of_frame (by grind only) frame
    have retRead : Readable t fr.rsp 8 := Readable.of_frame (by grind only) frame
    have call₁Read : Readable t 0x203dd0 8 := Readable.of_frame (by grind only) frame
    have call₂Read : Readable t 0x203e10 8 := Readable.of_frame (by grind only) frame
    grind only

theorem padLoop {fr : Activation} {a : Values Value Reg.count} {m : Ram} {key : ByteArray}
    (outer : Bool)
    (entry : Atom.All Extracted.programImage a m
      (Fn104970.frameAt (if outer then .l104ab0 else .l104a00) fr))
    (index : a[0] = ⟨64, 3⟩)
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (bytes : (⟨(fr.rsp - 488 + 8).toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key (if outer then 0x36 else 0))) :
    ∃ (b : Values Value Reg.count) (t : Ram),
      (if outer then (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l104ab0, a, m⟩, []⟩ ⟨⟨.l104ace, b, t⟩, []⟩
       else (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l104a00, a, m⟩, []⟩ ⟨⟨.l104a1e, b, t⟩, []⟩) ∧
      Atom.All Extracted.programImage b t (Fn104970.frameAt (if outer then .l104ace else .l104a1e) fr) ∧
      RamWriteFrame m t [⟨(fr.rsp - 488 + 8).toNat, 64⟩] ∧ b[14] = a[14] ∧
      (⟨(fr.rsp - 488 + 8).toNat, 64⟩ : MemoryRegion).HasBytes t (keyPad key (if outer then 0x5c else 0x36)) := by
  let sp := fr.rsp - 488
  have rsp : a[4] = ⟨64, sp⟩ := by
    cases outer <;> unfold_pad_entry entry fr <;> exact entry.1
  have stack : Writable Extracted.programImage m (fr.rsp - 1200) 1200 := by
    cases outer <;> unfold_pad_entry entry fr <;> grind only
  have start : (sp + 8).toNat = fr.rsp.toNat - 480 := padStart_toNat depth limit
  have lowNat : fr.low.toNat = fr.rsp.toNat - 1200 := by
    rw [low]
    exact BitVec.toNat_sub_of_le (show (1200 : BitVec 64) ≤ fr.rsp from depth)
  rw [← low] at stack
  have writePad : Writable Extracted.programImage m (sp + 8) 64 :=
    stack.sub (by rw [start, lowNat]; omega) (by rw [start, lowNat]; omega)
  obtain ⟨b, t, reach, writes, keep, padded⟩ :=
    runPadLoop outer (padHead outer) (padExit outer) (fun i => i.val ≠ 0 ∧ i.val ≠ 19)
      (by decide) rsp index writePad bytes (by
        intro a' m' j hj rsp' index' writable
        obtain ⟨b, run, counter, keep⟩ := xorPadStep outer hj rsp' index' writable
        exact ⟨b, run, counter, fun i hi => keep i hi.1 hi.2⟩)
  refine ⟨b, t, ?_, padFrame outer depth limit entry (fun i h0 h19 => keep i ⟨h0, h19⟩) writes,
    writes, keep 14 (by decide), padded⟩
  cases outer <;> exact reach

end K256.Proofs.Signing.UpdateV
