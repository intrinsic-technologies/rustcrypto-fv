import K256.Proofs.Generate.Generator.Multiply.State

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def writes (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp + 8).toNat, 0xe8⟩, ⟨(sp + 0xf8).toNat, 8⟩,
   ⟨(sp + 0x108).toNat, 0x98⟩, ⟨(sp + 0x1a8).toNat, 24⟩]

private theorem stack_address (sp : BitVec 64) (off : Nat) (bound : sp.toNat + off ≤ 2^32) :
    (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2^64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem body_outside {fr : Activation} (depth : 0xed8 ≤ fr.rsp.toNat)
    (_top : fr.rsp.toNat + 8 ≤ 2^32) {addr : BitVec 64} {len : Nat}
    (lo : fr.rsp.toNat - 0xcb8 + 0x1c0 ≤ addr.toNat)
    (hi : addr.toNat + len ≤ 2^32) :
    Outside (writes (fr.rsp - 0xcb8)) addr len := by
  let sp := fr.rsp - 0xcb8
  have hs : sp.toNat = fr.rsp.toNat - 0xcb8 := by
    apply BitVec.toNat_sub_of_le
    exact Nat.le_trans (by decide : 0xcb8 ≤ 0xed8) depth
  have ha (j : Nat) (hj : j ≤ 0x1c0) :
      (sp + BitVec.ofNat 64 j).toNat = fr.rsp.toNat - 0xcb8 + j := by
    rw [stack_address _ _ (by rw [hs]; omega), hs]
  refine ⟨by omega, ?_⟩
  intro r hr
  right
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · change (sp + 8).toNat + 0xe8 ≤ addr.toNat
    rw [show (sp+8).toNat = _ from ha 8 (by decide)]
    omega
  · change (sp + 0xf8).toNat + 8 ≤ addr.toNat
    rw [show (sp+0xf8).toNat = _ from ha 0xf8 (by decide)]
    omega
  · change (sp + 0x108).toNat + 0x98 ≤ addr.toNat
    rw [show (sp+0x108).toNat = _ from ha 0x108 (by decide)]
    omega
  · change (sp + 0x1a8).toNat + 24 ≤ addr.toNat
    rw [show (sp+0x1a8).toNat = _ from ha 0x1a8 (by decide)]
    omega

theorem body_frame {fr : Activation} {a b : Registers} {m out : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d880 fr))
    (save : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i])
    (frame : RamWriteFrame m out (writes (fr.rsp - 0xcb8))) :
    Atom.All Extracted.programImage b out (Fn11c880.frameAt .l11d810 fr) ∧
      Atom.All Extracted.programImage b out (Fn11c880.frameAt .l11f5e5 fr) := by
  obtain ⟨sp, df, mx, ftw, fcw, bx, sr12, sr13, sr14, sr15, bp, retRead, retAt, retLow,
    window, depth, aligned, gotARead, gotA, gotBRead, gotB, gotApart, _⟩ := atoms
  change fr.low.toNat + 0xed8 ≤ fr.rsp.toNat at depth
  have hDepth : 0xed8 ≤ fr.rsp.toNat := by omega
  have hTop := (show Readable m fr.rsp 8 from retRead).low
  have preserve (k : Nat) (hk : k ≤ 48) :
      memLoad out (fr.rsp - BitVec.ofNat 64 k) 64 =
        memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 := by
    have hK : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have eq : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
      rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 k).toNat ≤ _; omega), hK]
    apply frame.memLoad_eq
    exact body_outside hDepth hTop (by rw [eq]; omega) (by rw [eq]; omega)
  have preserveGot {addr : BitVec 64} (read : Readable m addr 8)
      (apart : fr.rsp.toNat ≤ addr.toNat ∨ addr.toNat + 0xee0 ≤ fr.rsp.toNat) :
      memLoad out addr 64 = memLoad m addr 64 := by
    rcases apart with h | h
    · exact frame.memLoad_eq (body_outside hDepth hTop (by omega) read.low)
    · refine frame.memLoad_eq ⟨by have := read.low; omega, ?_⟩
      intro r hr
      left
      have hs : (fr.rsp - 0xcb8).toNat = fr.rsp.toNat - 0xcb8 :=
        BitVec.toNat_sub_of_le (by exact Nat.le_trans (by decide : 0xcb8 ≤ 0xed8) hDepth)
      have atOff (j : Nat) (hj : j ≤ 0x1c0) :
          addr.toNat + 8 ≤ ((fr.rsp - 0xcb8) + BitVec.ofNat 64 j).toNat := by
        rw [stack_address _ _ (by rw [hs]; omega), hs]
        omega
      simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact atOff 8 (by decide)
      · exact atOff 0xf8 (by decide)
      · exact atOff 0x108 (by decide)
      · exact atOff 0x1a8 (by decide)
  have hgA : memLoad out 0x203de0 64 = 0x129770 := by
    apply (preserveGot (show Readable m 0x203de0 8 from gotARead) ?_).trans gotA
    change 0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0 at gotApart
    change fr.rsp.toNat ≤ 0x203de0 ∨ 0x203de0 + 0xee0 ≤ fr.rsp.toNat
    omega
  have hgB : memLoad out 0x203e20 64 = 0x100a20 := by
    apply (preserveGot (show Readable m 0x203e20 8 from gotBRead) ?_).trans gotB
    change 0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0 at gotApart
    change fr.rsp.toNat ≤ 0x203e20 ∨ 0x203e20 + 0xee0 ≤ fr.rsp.toNat
    omega
  have keepRet := (frame.memLoad_eq (body_outside hDepth hTop (by omega) hTop)).trans retAt
  have hfinal : Atom.All Extracted.programImage b out (Fn11c880.frameAt .l11d810 fr) :=
    ⟨(save 4 (by decide)).trans sp, (save 22 (by decide)).trans df,
      (save 39 (by decide)).trans mx, (save 50 (by decide)).trans ftw,
      (save 51 (by decide)).trans fcw, (preserve 48 (by decide)).trans bx,
      (preserve 40 (by decide)).trans sr12, (preserve 32 (by decide)).trans sr13,
      (preserve 24 (by decide)).trans sr14, (preserve 16 (by decide)).trans sr15,
      (preserve 8 (by decide)).trans bp, Readable.of_frame retRead frame, keepRet, retLow,
      Writable.of_frame window frame, depth, aligned, Readable.of_frame gotARead frame, hgA,
      Readable.of_frame gotBRead frame, hgB, gotApart, trivial⟩
  exact ⟨hfinal, hfinal⟩

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
