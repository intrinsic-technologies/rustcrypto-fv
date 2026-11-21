import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Memory
import K256.Proofs.Signing.UpdateV

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

private def valueChild (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (ret : BitVec 64) : Activation :=
  {fr with
    original := m, rsp := fr.rsp - 720, low := fr.rsp - 1920, ret := ret,
    rbx := a[3].get 64, rbp := a[5].get 64, r12 := a[12].get 64, r13 := a[13].get 64,
    r14 := a[14].get 64, r15 := a[15].get 64, rsi := a[6].get 64, rdx := a[2].get 64,
    rcx := a[1].get 64, r8 := a[8].get 64, r9 := a[9].get 64 }

private theorem savedValue (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  obtain ⟨w, x⟩ := v
  cases h
  rfl

private theorem ValueCall.saved {second input fr a m state}
    (e : ValueCall second input fr a m state) (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
    a[i] = ⟨64, a[i].get 64⟩ := by
  apply savedValue
  have width := e.live.savedWidths i hi
  have ne : i.val ≠ 4 := by intro eq; simp [Activation.calleeSavedNumbers, eq] at hi
  simpa only [Fin.getElem_fin, Vector.getElem_set, Ne.symm ne, reduceIte] using width

private theorem ValueCall.common {second input fr a m state}
    (e : ValueCall second input fr a m state) :
    Atom.All Extracted.programImage (a.set 4 ⟨64, sp fr⟩) m (Fn103f30.frameAt .l104918 fr) := by
  have atoms := e.live.atoms
  cases second
  · cases input
    · obtain ⟨s, d, _, _, _, x, y, z, tail⟩ := atoms
      exact ⟨s, d, x, y, z, tail⟩
    · obtain ⟨s, d, _, x, y, z, _, tail⟩ := atoms
      exact ⟨s, d, x, y, z, tail⟩
  · exact atoms

private theorem valueEntry {second input fr a m state} (env : Environment fr input)
    (e : ValueCall second input fr a m state) :
    Atom.All Extracted.programImage a m (Fn104970.frameAt .l104970
      (valueChild fr a m (valueReturn second input))) := by
  obtain ⟨_, df, mx, ft, fc, _, _, _, _, _, _, _, _, _, win, _, align, rcp, cp, rset, st, gap, _⟩ := e.common
  simp only [Atom.Holds, Fin.getElem_fin, Vector.getElem_set] at df mx ft fc
  change Writable _ m (fr.rsp - 1920) 1920 at win
  change fr.rsp.toNat % 16 = 8 at align
  change 0x204598 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at gap
  have norm : sp fr - 8 = fr.rsp - 720 := by unfold sp; bv_omega
  have bound := env.depth
  have limit := env.limit
  have off (k : BitVec 64) (hk : k.toNat ≤ 1920) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have stack : Writable Extracted.programImage m (fr.rsp - 720 - 1200) 1200 := by
    rw [show fr.rsp - 720 - 1200 = fr.rsp - 1920 by bv_omega]
    apply win.sub (Nat.le_refl _) (by omega)
  have read : Readable m (fr.rsp - 720) 8 := win.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have retLow : (valueReturn second input).toNat < 2^32 := by
    cases second <;> cases input <;> simp only [valueReturn, seeded, Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;> decide
  simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds, Atom.gpr, valueChild]
  refine ⟨norm ▸ e.rsp, df, savedValue _ (e.widths 1 (by decide)), savedValue _ (e.widths 2 (by decide)),
    e.saved 3 (by decide), e.saved 5 (by decide), savedValue _ (e.widths 6 (by decide)), e.dst,
    savedValue _ (e.widths 8 (by decide)), savedValue _ (e.widths 9 (by decide)), e.saved 12 (by decide),
    e.saved 13 (by decide), e.saved 14 (by decide), e.saved 15 (by decide), mx, ft, fc, read, norm ▸ e.returned,
    retLow, stack, ?_, ?_, rcp, cp, rset, st, ?_, trivial⟩ <;>
    simp (disch := decide) only [off, BitVec.reduceToNat] <;> omega

private theorem ValueCall.rsi {second input fr a m state}
    (entry : ValueCall second input fr a m state) (go : (!second && seeded input) = true) :
    a[14] = ⟨64, fr.rsi⟩ := by
  have h := entry.live.atoms
  cases second <;> cases input <;> try contradiction
  obtain ⟨_, _, rs, _⟩ := h
  change (a.set 4 ⟨64, sp fr⟩)[14] = ⟨64, fr.rsi⟩ at rs
  simpa using rs

private theorem valueBytesAfter {fr : Activation} {state : State} {m n : Ram} {rs : List MemoryRegion}
    (before : StateAt m fr.rdi state) (writes : RamWriteFrame m n rs) (keyOut : Outside rs fr.rdi 32)
    (value : (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes n
      (HMAC.hmac SHA256.hashBytes 64 state.key state.value)) :
    StateAt n fr.rdi (Drbg.updateValue state) := by
  have h := UpdateV.Finalize.bytesAfter (n := 32) (bs := state.key) writes keyOut before.key
  unfold Drbg.updateValue
  exact ⟨h, value⟩

theorem resumeRoundValue {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (entry : ValueCall second input fr a m state) :
    ∃ b n, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104970, a, m⟩, [Verify.resumeAt (resume second input) (valueReturn second input)]⟩
      ⟨⟨resume second input, b, n⟩, []⟩ ∧
      Live (resume second input) fr b n (Drbg.updateValue state) ∧
      ((!second && seeded input) = true → Slots fr n) := by
  let child := valueChild fr a m (valueReturn second input)
  have dep := env.depth
  have lim := env.limit
  have dataLim := env.dataLow
  have off (k : BitVec 64) (hk : k.toNat ≤ 1920) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have base : fr.low.toNat = fr.rsp.toNat - 1920 := by rw [env.low, off _ (by decide)]; rfl
  have cs : child.rsp.toNat = fr.rsp.toNat - 720 := off 720 (by decide)
  have cl : child.low.toNat = fr.rsp.toNat - 1920 := off 1920 (by decide)
  have apart : child.rdi.toNat + 64 ≤ child.low.toNat ∨ child.rsp.toNat + 8 ≤ child.rdi.toNat := by
    change fr.rdi.toNat + 64 ≤ child.low.toNat ∨ child.rsp.toNat + 8 ≤ fr.rdi.toNat
    rcases env.apart with h | h <;> omega
  obtain ⟨out, run, tag', post, wr, widths, value⟩ := UpdateV.execution (fr := child) (key := state.key) (value := state.value)
    (valueEntry env entry) (entry.live.image env)
    (show fr.rsp - 1920 = fr.rsp - 720 - 1200 by bv_omega) (by omega) (by omega)
    dataLim apart (env.writable.of_frame entry.live.writes) entry.live.bytes.key entry.live.bytes.value
  have ret := ParseSignature.exec_reaches_resume run (Verify.resumeAt (resume second input) (valueReturn second input)) []
    (by rw [tag']; exact decide_eq_true (rfl : Value.mk 64 child.ret = Value.mk 64 child.ret))
  have footprint : RamWriteFrame m out.store [child.region, ⟨fr.rdi.toNat + 32, 32⟩] := wr
  have total := entry.live.writes.trans footprint (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
        simp only [Activation.region, cl, cs, base] <;> omega
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by change fr.rdi.toNat ≤ fr.rdi.toNat + 32; omega,
        by change fr.rdi.toNat + 32 + 32 ≤ fr.rdi.toNat + 64; omega⟩)
  have keyOutside : Outside [child.region, ⟨fr.rdi.toNat + 32, 32⟩] fr.rdi 32 := by
    refine ⟨by omega, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · change _ ≤ child.low.toNat ∨ child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ _
      rcases env.apart with h | h <;> omega
    · obtain rfl := List.mem_singleton.mp h; exact Or.inl (Nat.le_refl _)
  have keep (k : BitVec 64) (h : k.toNat ≤ 712) :
      memLoad out.store (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply footprint.memLoad_eq
    have addr := off k (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · right; change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ _; omega
    · obtain rfl := List.mem_singleton.mp hr
      change (fr.rsp - k).toNat + 8 ≤ fr.rdi.toNat + 32 ∨ fr.rdi.toNat + 32 + 32 ≤ (fr.rsp - k).toNat
      rcases env.apart with h | h <;> omega
  have atZero := keep 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at atZero
  have getSlot (off : BitVec 64) (d : BitVec 64) (h : d.toNat ≤ 712)
      (eq : sp fr + off = fr.rsp - d) :
      memLoad out.store (sp fr + off) 64 = memLoad m (sp fr + off) 64 := eq ▸ keep d h
  have slots (hs : seeded input = true) : Slots fr out.store := by
    obtain ⟨stop, val, statePtr⟩ := entry.slots hs
    exact ⟨(getSlot 8 704 (by decide) (by unfold sp; bv_omega)).trans stop,
      (getSlot 112 600 (by decide) (by unfold sp; bv_omega)).trans val,
      (getSlot 120 592 (by decide) (by unfold sp; bv_omega)).trans statePtr⟩
  obtain ⟨rs, df, bx, bp, r12, r13, r14, r15, mx, ft, fc, _⟩ := post
  have saved : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → out.values[i] = a[i] := by
    intro ⟨i, hi⟩ mem
    have eq := entry.saved ⟨i, hi⟩ mem
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> refine Eq.trans ?_ eq.symm
    · exact bx
    · exact bp
    · exact r12
    · exact r13
    · exact r14
    · exact r15
  have rs' : out.values[4] = ⟨64, sp fr⟩ := rs.trans (congrArg (Value.mk 64)
    (show fr.rsp - 720 + 8 = sp fr by unfold sp; bv_omega))
  obtain ⟨_, _, _, _, _, sb, s12, s13, s14, s15, s5, rd, rt, rtLow, win, bound, align,
    _, _, _, _, gap, _⟩ := entry.common
  change Readable m fr.rsp 8 at rd
  change Writable _ m (fr.rsp - 1920) 1920 at win
  have atoms : Atom.All Extracted.programImage out.values out.store (Fn103f30.frameAt .l104951 fr) := by
    exact ⟨rs', df, mx, ft, fc, (keep 48 (by decide)).trans sb, (keep 40 (by decide)).trans s12,
      (keep 32 (by decide)).trans s13, (keep 24 (by decide)).trans s14, (keep 16 (by decide)).trans s15,
      (keep 8 (by decide)).trans s5, rd.of_frame wr, atZero.trans rt, rtLow, win.of_frame wr,
      bound, align, trivial⟩
  have updatedBytes := valueBytesAfter (fr := fr) (state := state) entry.live.bytes footprint keyOutside value
  have nextWidths (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) : out.values[i].width = 64 := by
    rw [saved i hi]
    exact congrArg Value.width (entry.saved i hi)
  refine ⟨out.values, out.store, ret, ⟨?_, total, updatedBytes, fun _ => widths, nextWidths⟩,
    fun h => slots (Bool.and_eq_true_iff.mp h).2⟩
  by_cases go : (!second && seeded input) = true
  · rw [resume, ite_eq_left go]
    have rsi := entry.rsi go
    have liveSlots := slots (Bool.and_eq_true_iff.mp go).2
    have save : memLoad out.store (fr.rsp - 592) 64 = fr.rdi := by
      simpa only [sp, Lift.reduceAddOffset] using liveSlots.state
    have tables := Fn103f30.callSlots_loaded (sections := Extracted.programSections)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (env.imageAt total)
    obtain ⟨rcp, cp⟩ := tables (0x203dd0, 0x12a820) (by decide)
    obtain ⟨rset, st⟩ := tables (0x203e10, 0x12a700) (by decide)
    obtain ⟨rsp, direction, mxcsr, ftw, fcw, sb, s12, s13, s14, s15, s5, rd, rt, rtLow, win,
      bound, align, _⟩ := atoms
    exact ⟨rsp, direction, (saved 3 (by decide)).trans (entry.bx go), (saved 14 (by decide)).trans rsi,
      mxcsr, ftw, fcw, save, sb, s12, s13, s14, s15, s5, rd, rt, rtLow, win,
      bound, align, rcp, cp, rset, st, gap, trivial⟩
  · simpa only [resume, go, Bool.false_eq_true, ↓reduceIte] using atoms

end K256.Proofs.Signing.Nonce.Initialize.Update
