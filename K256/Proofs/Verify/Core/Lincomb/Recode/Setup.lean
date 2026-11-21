import K256.Proofs.Verify.Core.Lincomb.Recode.Return

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

structure LoopRegisters (original current : Registers) (sp : BitVec 64) (i c : Nat) : Prop where
  stack : current[4] = ⟨64, sp-136⟩
  width : current[12] = ⟨64, 5⟩
  bitIndex : current[15] = ⟨64, BitVec.ofNat 64 i⟩
  length : current[14] = ⟨64, BitVec.ofNat 64 i⟩
  negIndex : current[5] = ⟨64, -(BitVec.ofNat 64 i)⟩
  carry : current[13] = ⟨64, BitVec.ofNat 64 c⟩
  saved : ControlSaved original current

structure LoopMemory (m : Ram) (sp dst : BitVec 64) : Prop where
  limit : memLoad m (sp-136) 64 = 257
  radix : memLoad m (sp-124) 32 = 32
  buffer : memLoad m (sp-120) 64 = dst
  bits : memLoad m (sp-112) 64 = 128
  half : memLoad m (sp-104) 64 = 16
  mask : memLoad m (sp-96) 64 = 31

private abbrev writeBits (m : Ram) (sp : BitVec 64) : Ram :=
  memStore m (sp-112) (128 : BitVec 64)

abbrev writeLocals (m : Ram) (sp : BitVec 64) : Ram :=
  let m₁ := memStore (writeBits m sp) (sp-136) (257 : BitVec 64)
  let m₂ := memStore m₁ (sp-96) (31 : BitVec 64)
  let m₃ := memStore m₂ (sp-104) (16 : BitVec 64)
  memStore m₃ (sp-124) (32 : BitVec 32)

theorem writeLocalsMemory {m : Ram} {sp dst : BitVec 64}
    (dstWord : memLoad m (sp-120) 64 = dst) : LoopMemory (writeLocals m sp) sp dst := by
  constructor <;>
    simp (disch := store_disch) only [writeLocals, writeBits, memLoad_memStore_same,
      memLoad_memStore_of_rangeApart, dstWord]

theorem writeLocalsFrame {m : Ram} {sp : BitVec 64}
    (room : 136 ≤ sp.toNat) (low : sp.toNat ≤ 2^32) :
    RamWriteFrame m (writeLocals m sp) [⟨sp.toNat-136, 48⟩] := by
  have slot {off : BitVec 64} {len : Nat} (lower : off.toNat ≤ 136) (upper : 88+len ≤ off.toNat) :
      InRegions [⟨sp.toNat-136, 48⟩] (sp-off) len := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change sp.toNat-136 ≤ (sp-off).toNat ∧ (sp-off).toNat + len ≤ sp.toNat-136+48 ∧
      (sp-off).toNat + len ≤ 2^64
    rw [subNat (by omega)]
    omega
  unfold writeLocals writeBits
  repeat' apply RamWriteFrame.memStore _ _ (slot (by decide) (by decide))
  exact .refl _ _

theorem enterLoop {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4] = ⟨64, sp-136⟩) (limit : a[15].get 64 = 257) (bits : a[13].get 64 = 128)
    (width : a[12] = ⟨64, 5⟩) (radix : a[3].get 64 = 32)
    (w : Writable Extracted.programImage m (sp-136) 48) :
    ∃ b c,
      program.runBlock machine ⟨.l1107ea, a, m⟩ = .jump ⟨.l1107fb, b, writeBits m sp⟩ ∧
      program.runBlock machine ⟨.l1107fb, b, writeBits m sp⟩ = .jump ⟨.l110847, c, writeLocals m sp⟩ ∧
      LoopRegisters a c sp 0 0 := by
  have localWord (off : BitVec 64) (len : Nat) (fit : (off - (-136 : BitVec 64)).toNat + len ≤ 48) :
      Writable Extracted.programImage m (sp+off) len :=
    w.of_offsets rfl (by bv_omega) fit
  have w0 : StoreOk Extracted.programImage m (sp-112) 8 0x1107ed 5 := by
    have wr := localWord (-112) 8 (by decide)
    have loc : sp + (-112) = sp-112 := by bv_omega
    rw [loc] at wr
    exact storeGuard (off := 3) wr code_l1107ea (by decide)
  let m₀ := writeBits m sp
  let m₁ := memStore m₀ (sp-136) (257 : BitVec 64)
  let m₂ := memStore m₁ (sp-96) (31 : BitVec 64)
  let m₃ := memStore m₂ (sp-104) (16 : BitVec 64)
  have w1 : StoreOk Extracted.programImage m₀ (sp-136) 8 0x1107fb 4 :=
    storeGuard (off := 0) ((w.of_offsets (addr_self _) (addr_self _) (by decide : (0-0 : BitVec 64).toNat + 8 ≤ 48)).memStore
      (sp-112) (128 : BitVec 64)) code_l1107fb (by decide)
  have w2 : StoreOk Extracted.programImage m₁ (sp-96) 8 0x110803 5 := by
    have wr := ((localWord (-96) 8 (by decide)).memStore (sp-112) (128 : BitVec 64)).memStore
      (sp-136) (257 : BitVec 64)
    have loc : sp + (-96) = sp-96 := by bv_omega
    rw [loc] at wr
    exact storeGuard (off := 8) wr code_l1107fb (by decide)
  have w3 : StoreOk Extracted.programImage m₂ (sp-104) 8 0x11080e 5 := by
    have wr := (((localWord (-104) 8 (by decide)).memStore (sp-112) (128 : BitVec 64)).memStore
      (sp-136) (257 : BitVec 64)).memStore (sp-96) (31 : BitVec 64)
    have loc : sp + (-104) = sp-104 := by bv_omega
    rw [loc] at wr
    exact storeGuard (off := 19) wr code_l1107fb (by decide)
  have w4 : StoreOk Extracted.programImage m₃ (sp-124) 4 0x110816 4 := by
    have wr := ((((localWord (-124) 4 (by decide)).memStore (sp-112) (128 : BitVec 64)).memStore
      (sp-136) (257 : BitVec 64)).memStore (sp-96) (31 : BitVec 64)).memStore (sp-104) (16 : BitVec 64)
    have loc : sp + (-124) = sp-124 := by bv_omega
    rw [loc] at wr
    exact storeGuard (off := 27) wr code_l1107fb (by decide)
  have hsp : a[4].get 64 = sp-136 := congrArg (Value.get 64) rsp
  refine ⟨?_, ?_, ?first, ?next, ?regs⟩
  case first =>
    cfg_eval [hsp, bits, w0, testFlags, show ((128 : BitVec 64) == 0) = false by decide]
    rfl
  case next =>
    cfg_eval [hsp, limit, radix, w1, w2, w3, w4]
    rw [ite_eq_left w1, ite_eq_left w2, ite_eq_left w3, ite_eq_left w4]
  case regs =>
    refine ⟨rsp, width, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, bound⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Recode
