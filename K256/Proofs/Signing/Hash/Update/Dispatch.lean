import K256.Proofs.Signing.Hash.Update.Slice

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

set_option maxRecDepth 2048 in
theorem dispatch {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {message : ByteArray}
    (rsp : a[4] = ⟨64, sp⟩) (direction : a[22] = ⟨1, 0⟩)
    (count : a[1] = ⟨64, 1⟩) (slice : a[2] = ⟨64, sp + 1136⟩)
    (pointer : memLoad m (sp + 1136) 64 = src)
    (size : memLoad m (sp + 1144) 64 = BitVec.ofNat 64 message.size)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + message.size < 2^32)
    (buffered : memLoad m (sp + 551) 8 = 0) :
    ∃ b, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1054a6, a, m⟩, []⟩ ⟨⟨target message.size, b, m⟩, []⟩ ∧
      Slice sp src message.size b ∧
      ∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i] := by
  have readStack {offset length : Nat} (within : offset + length ≤ 1160) :
      LoadOk m (sp + BitVec.ofNat 64 offset) length := by
    have base : (sp - 512).toNat = sp.toNat - 512 :=
      BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
    have addr : (sp + BitVec.ofNat 64 offset).toNat = sp.toNat + offset := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
        Nat.mod_eq_of_lt (by omega)]
    exact LoadOk.of_region stack.readable (by omega) (by omega)
  have readPointer : LoadOk m (sp + 1136) 8 := readStack (offset := 1136) (by decide)
  have readSize : LoadOk m (sp + 1144) 8 := readStack (offset := 1144) (by decide)
  have readBuffered : LoadOk m (sp + 551) 1 := readStack (offset := 551) (by decide)
  have carry : (subSpec (BitVec.ofNat 64 message.size) 64).2.CF =
      decide (message.size < 64) := by
    change decide ((BitVec.ofNat 64 message.size).toNat < 64) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : message.size < 2^64)]
  have sliceEnd : (16 : BitVec 64) + (sp + 1136) = sp + 1152 := by bv_omega
  have sizeAddress : (sp + 1136 : BitVec 64) + 8 = sp + 1144 := by bv_omega
  have countGet : a[1].get 64 = 1 := by rw [count, Value.get_mk]
  have sliceGet : a[2].get 64 = sp + 1136 := by rw [slice, Value.get_mk]
  have setup : ∃ c : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1054a6, a, m⟩ =
        .jump ⟨.l1054e9, c, m⟩ ∧
      c[3] = ⟨64, sp + 1152⟩ ∧ c[4] = ⟨64, sp⟩ ∧
      c[14] = ⟨64, sp + 1136⟩ ∧ c[15] = ⟨64, 0x12a820⟩ ∧ c[22] = ⟨1, 0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [39,50,51] → c[i] = a[i]) := by
    refine ⟨?_, ?run, ?post⟩
    case run =>
      cfg_eval [countGet, sliceGet, sliceEnd]
      rfl
    case post =>
      refine ⟨rfl, rsp, rfl, rfl, direction, ?_⟩
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
  obtain ⟨c, setup, stop, csp, cslice, memcpy, df, saved⟩ := setup
  have spGet : c[4].get 64 = sp := by rw [csp, Value.get_mk]
  have sliceBase : c[14].get 64 = sp + 1136 := by rw [cslice, Value.get_mk]
  have zeroExtend : (0 : BitVec 8).setWidth 64 = 0 := rfl
  have route : ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1054e9, c, m⟩ =
        .jump ⟨target message.size, b, m⟩ ∧ Slice sp src message.size b ∧
      (∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = c[i]) := by
    refine ⟨?_, ?run, ?post⟩
    case run =>
      cfg_eval [spGet, sliceBase, sizeAddress, readPointer, readSize, readBuffered, pointer, size,
        buffered, zeroExtend, BitVec.sub_zero, carry]
      simp only [decide_eq_true_eq]
      split
      · rename_i short
        rw [show target message.size = .l1054c0 from ite_eq_left short]
      · rename_i long
        rw [show target message.size = .l105509 from ite_eq_right long]
    case post =>
      refine ⟨⟨csp, df, stop, rfl, rfl, rfl, rfl, cslice, memcpy⟩, ?_⟩
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
  obtain ⟨b, route, args, keep⟩ := route
  exact ⟨b, .step (congrArg (Transfer.next _ []) setup)
    (Semantics.Reaches.single (congrArg (Transfer.next _ []) route)),
    args, fun i hi => (keep i hi).trans (saved i hi)⟩

end Update
end K256.Proofs.Signing.Hash
