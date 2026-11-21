import K256.Proofs.Verify.Core.Lincomb.Prepare.Digits.Blocks
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev digitWhole (sp digits : BitVec 64) : List MemoryRegion :=
  [scratch sp 0x558, ⟨digits.toNat, 544⟩]

abbrev serializeWrites (sp : BitVec 64) : List MemoryRegion :=
  [scratch (frameSp sp) 0x118, ⟨(digitTemp sp).toNat, 32⟩]

abbrev recodeWrites (sp dst : BitVec 64) : List MemoryRegion :=
  [scratch (frameSp sp) 0x118, ⟨dst.toNat, 257⟩]

theorem digitStackNat {sp : BitVec 64} (room : 0x558 ≤ sp.toNat) {off : BitVec 64}
    (h : off.toNat ≤ 0x558) : (sp - off).toNat = sp.toNat - off.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))

theorem digitFrameNat {sp : BitVec 64} (room : 0x558 ≤ sp.toNat) {off : Nat}
    (h : off ≤ 0x2b8) :
    (frameSp sp + BitVec.ofNat 64 off).toNat = sp.toNat - 0x2b8 + off := by
  have base := digitStackNat room (off := 0x2b8) (by decide)
  have top := sp.isLt
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  rw [BitVec.toNat_add, base, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem digitOffsetNat {digits : BitVec 64} (low : digits.toNat + 544 ≤ 2^64) {off : Nat}
    (h : off < 544) : (digits + BitVec.ofNat 64 off).toNat = digits.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem digitScratchWindow {a : Registers} {m n : Ram} {sp digits : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (frame : RamWriteFrame m n (digitWhole sp digits))
    {off len : Nat} (h : off + len ≤ 0x2b8) :
    Writable Extracted.programImage n (frameSp sp + BitVec.ofNat 64 off) len := by
  have base := digitStackNat entry.room (off := 0x558) (by decide)
  have dest := digitFrameNat entry.room (off := off) (by omega)
  change (sp - 0x558).toNat = sp.toNat - 0x558 at base
  have w : Writable Extracted.programImage n (sp - 0x558) 0x558 := entry.stack.of_frame frame
  apply w.sub
  all_goals rw [base, dest] <;> omega

theorem digitBufferWindow {m n : Ram} {sp digits : BitVec 64}
    (w : Writable Extracted.programImage m digits 544)
    (frame : RamWriteFrame m n (digitWhole sp digits)) {off len : Nat}
    (h : off < 544) (fit : off + len ≤ 544) :
    Writable Extracted.programImage n (digits + BitVec.ofNat 64 off) len := by
  have low : digits.toNat + 544 ≤ 2^32 := w.readable.low
  have offNat := digitOffsetNat (by omega : digits.toNat + 544 ≤ 2^64) h
  exact (w.of_frame frame).sub (by omega) (by omega)

theorem digitPushFrame {m : Ram} {sp : BitVec 64} (room : 0x558 ≤ sp.toNat) (ret : BitVec 64)
    {regions : List MemoryRegion} (member : scratch (frameSp sp) 0x118 ∈ regions) :
    RamWriteFrame m (memStore m (digitCallSp sp) ret) regions := by
  apply (RamWriteFrame.refl _ _).memStore
  refine ⟨_, member, ?_⟩
  have push : digitCallSp sp = sp - 0x2c0 := by unfold digitCallSp frameSp; bv_omega
  have base := digitStackNat room (off := 0x2b8) (by decide)
  have addr := digitStackNat room (off := 0x2c0) (by decide)
  have top := sp.isLt
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  change (sp - 0x2c0).toNat = sp.toNat - 0x2c0 at addr
  simp only [InRegion, scratch, push, base, addr]
  omega

theorem serializeWithin {sp digits : BitVec 64} (room : 0x558 ≤ sp.toNat) :
    RegionsWithin (serializeWrites sp) (digitWhole sp digits) := by
  have base := digitStackNat room (off := 0x2b8) (by decide)
  have temp := digitFrameNat room (off := 0x38) (by decide)
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  change (digitTemp sp).toNat = sp.toNat - 0x2b8 + 0x38 at temp
  intro r hr
  refine ⟨_, .head _, ?_⟩
  simp only [serializeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [scratch, base, temp] <;> omega

theorem recodeWithin {sp digits dst : BitVec 64} (room : 0x558 ≤ sp.toNat)
    (lo : digits.toNat ≤ dst.toNat) (hi : dst.toNat + 257 ≤ digits.toNat + 544) :
    RegionsWithin (recodeWrites sp dst) (digitWhole sp digits) := by
  have base := digitStackNat room (off := 0x2b8) (by decide)
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  intro r hr
  simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, .head _, by simp only [scratch, base]; omega⟩
  · exact ⟨_, .tail _ (.head _), lo, hi⟩

private theorem digitCodeApart {m : Ram} {b : BitVec 64} {len : Nat}
    (w : Writable Extracted.programImage m b len) {v : BitVec 64 × UInt8}
    (hv : v ∈ Extracted.programImage) :
    v.1.toNat + 1 ≤ b.toNat ∨ b.toNat + len ≤ v.1.toNat := by
  apply Classical.byContradiction
  intro denied
  apply w.notCode v hv (v.1.toNat - b.toNat) (by omega)
  rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem digitImage {a : Registers} {m n : Ram} {sp digits : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (w : Writable Extracted.programImage m digits 544)
    (frame : RamWriteFrame m n (digitWhole sp digits)) :
    ∀ v ∈ Extracted.programImage, n[v.1]? = some v.2 := by
  intro v hv
  rw [frame.outside _ ⟨by have := v.1.isLt; omega, ?_⟩]
  · exact entry.image v hv
  intro r hr
  simp only [digitWhole, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have h := digitCodeApart entry.stack hv
    have eq := digitStackNat entry.room (off := 0x558) (by decide)
    change (sp - 0x558).toNat = sp.toNat - 0x558 at eq
    change v.1.toNat + 1 ≤ (sp - 0x558).toNat ∨ (sp - 0x558).toNat + 0x558 ≤ v.1.toNat at h
    rw [eq] at h
    exact h
  · exact digitCodeApart w hv

theorem stackOutsideSerialize {sp : BitVec 64} (room : 0x558 ≤ sp.toNat) {off len : Nat}
    (fit : off + len ≤ 0x2b8) (apart : off + len ≤ 0x38 ∨ 0x58 ≤ off) :
    Outside (serializeWrites sp) (frameSp sp + BitVec.ofNat 64 off) len := by
  have base := digitStackNat room (off := 0x2b8) (by decide)
  have addr := digitFrameNat room (off := off) (by omega)
  have temp := digitFrameNat room (off := 0x38) (by decide)
  have top := sp.isLt
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  change (digitTemp sp).toNat = sp.toNat - 0x2b8 + 0x38 at temp
  refine ⟨by omega, fun r hr => ?_⟩
  simp only [serializeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right; simp only [scratch, base]; omega
  · simp only [temp, addr]; omega

theorem stackOutsideRecode {sp digits dst : BitVec 64} (room : 0x558 ≤ sp.toNat)
    (sep : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (lo : digits.toNat ≤ dst.toNat) (hi : dst.toNat + 257 ≤ digits.toNat + 544)
    {off len : Nat} (fit : off + len ≤ 0x2b8) :
    Outside (recodeWrites sp dst) (frameSp sp + BitVec.ofNat 64 off) len := by
  have base := digitStackNat room (off := 0x2b8) (by decide)
  have addr := digitFrameNat room (off := off) (by omega)
  have top := sp.isLt
  have apart := sep.2 _ (List.mem_cons_self ..)
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  refine ⟨by omega, fun r hr => ?_⟩
  simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right; simp only [scratch, base]; omega
  · dsimp only [scratch] at apart
    simp only [addr]
    omega

theorem bufferOutsideSerialize {sp digits : BitVec 64} (room : 0x558 ≤ sp.toNat)
    (sep : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    {off len : Nat} (hl : off < 544) (fit : off + len ≤ 544) :
    Outside (serializeWrites sp) (digits + BitVec.ofNat 64 off) len := by
  have addr := digitOffsetNat sep.1 hl
  have apart := sep.2 _ (List.mem_cons_self ..)
  have low := sep.1
  have base := digitStackNat room (off := 0x2b8) (by decide)
  have temp := digitFrameNat room (off := 0x38) (by decide)
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  change (digitTemp sp).toNat = sp.toNat - 0x2b8 + 0x38 at temp
  refine ⟨by omega, fun r hr => ?_⟩
  simp only [serializeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  dsimp only [scratch] at apart
  rcases hr with rfl | rfl <;> simp only [scratch, base, temp, addr] <;> omega

theorem bufferOutsideRecode {sp digits dst : BitVec 64} (room : 0x558 ≤ sp.toNat)
    (sep : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    {off len : Nat} (hl : off < 544) (fit : off + len ≤ 544)
    (other : digits.toNat + off + len ≤ dst.toNat ∨ dst.toNat + 257 ≤ digits.toNat + off) :
    Outside (recodeWrites sp dst) (digits + BitVec.ofNat 64 off) len := by
  have addr := digitOffsetNat sep.1 hl
  have apart := sep.2 _ (List.mem_cons_self ..)
  have low := sep.1
  have base := digitStackNat room (off := 0x2b8) (by decide)
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  refine ⟨by omega, fun r hr => ?_⟩
  simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · dsimp only [scratch] at apart
    simp only [scratch, base, addr]
    omega
  · simpa only [addr] using other

end K256.Proofs.Verify.Core.Lincomb.Prepare
