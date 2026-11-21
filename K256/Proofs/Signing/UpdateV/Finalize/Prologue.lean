import K256.Proofs.Signing.UpdateV.Finalize.State
import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private def compressResume : StackFrame Value Label signature Reg.count :=
  ⟨.l107adb, #v[], rfl, some ⟨64, 0x107adb⟩⟩


private def compressionMemory (a : Registers) (m : Ram) (sp : BitVec 64) : Ram :=
  let t := memStore m (sp - 8) (a[5].get 64)
  let t := memStore t (sp - 16) (a[15].get 64)
  let t := memStore t (sp - 24) (a[14].get 64)
  let t := memStore t (sp - 32) (a[13].get 64)
  let t := memStore t (sp - 40) (a[12].get 64)
  let t := memStore t (sp - 48) (a[3].get 64)
  let t := memStore t (sp - 64) (0x5be0cd191f83d9ab#64)
  let t := memStore t (sp - 72) (0x9b05688c510e527f#64)
  let t := memStore t (sp - 80) (0xa54ff53a3c6ef372#64)
  let t := memStore t (sp - 88) (0xbb67ae856a09e667#64)
  let t := memStore t (sp - 89) (0#8)
  let t := memStore t (sp - 56) (1#64)
  memStore t (sp - 368) (0x107adb#64)

set_option maxHeartbeats 1000000 in
private theorem setupCompression {a : Registers} {m : Ram} {sp src dst : BitVec 64}
    (call : Call a m sp src dst) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l107a50, a, m⟩ =
      .call ⟨.l1218e0, b, compressionMemory a m sp⟩ compressResume ∧
      b[4].get 64 = sp - 368 ∧ b[7].get 64 = sp - 88 ∧ b[6].get 64 = src ∧
      b[2].get 64 = 1 ∧ b[3] = ⟨64, dst⟩ ∧ b[14] = ⟨64, sp - 88⟩ ∧
      b[15] = ⟨64, src⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5, 12, 13, 22, 39, 50, 51] → b[i] = a[i] := by
  have rsp := congrArg (Value.get 64) call.rsp
  have rsi := congrArg (Value.get 64) call.out
  have rdi := congrArg (Value.get 64) call.ctx
  have stack := call.stack
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp, rsi, rdi]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l107a50)
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem stackAddress {sp : BitVec 64} (depth : 704 ≤ sp.toNat)
    {off : Nat} (bound : off ≤ 704) :
    (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := by
  have h : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h]; omega), h]

private theorem compressionMemory_frame (a : Registers) (m : Ram) {sp : BitVec 64}
    (depth : 704 ≤ sp.toNat) :
    RamWriteFrame m (compressionMemory a m sp) [scratch sp] := by
  have slot (off : BitVec 64) (n : Nat) (bound : n ≤ off.toNat ∧ off.toNat ≤ 704) :
      InRegions [scratch sp] (sp - off) n := by
    have hs : off.toNat ≤ sp.toNat := Nat.le_trans bound.2 depth
    have pos : (sp - off).toNat = sp.toNat - off.toNat := BitVec.toNat_sub_of_le hs
    refine ⟨scratch sp, List.mem_singleton_self _, ?_⟩
    change sp.toNat - 704 ≤ (sp - off).toNat ∧
      (sp - off).toNat + n ≤ sp.toNat - 704 + 704 ∧ (sp - off).toNat + n ≤ 2 ^ 64
    rw [pos]
    have endLe : sp.toNat - off.toNat + n ≤ sp.toNat :=
      Nat.le_trans (Nat.add_le_add_left bound.1 _) (Nat.le_of_eq (Nat.sub_add_cancel hs))
    exact ⟨Nat.sub_le_sub_left bound.2 _, by rwa [Nat.sub_add_cancel depth],
      Nat.le_trans endLe (Nat.le_of_lt sp.isLt)⟩
  unfold compressionMemory
  iterate 13 apply RamWriteFrame.memStore _ _ (slot _ _ (by decide))
  exact .refl _ _

private theorem compressionMemory_state (a : Registers) (m : Ram) (sp : BitVec 64) :
    Compression.StateAt (compressionMemory a m sp) (sp - 88) initialHash := by
  refine ⟨by decide +kernel, ?_⟩
  intro i hi
  have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases index with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, compressionMemory,
      Vector.getElem_ofFn] <;>
    segment_words [] <;> decide +kernel

private theorem compressionMemory_slots (a : Registers) (m : Ram) (sp : BitVec 64) (i : Fin 6) :
    memLoad (compressionMemory a m sp) (sp - (#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i]) 64 =
      a[(#v[3, 5, 12, 13, 14, 15] : Vector (Fin Reg.count) 6)[i]].get 64 := by
  obtain ⟨i, hi⟩ := i
  have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases index with rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold compressionMemory <;> segment_words [] <;> rfl

private theorem compressionMemory_count (a : Registers) (m : Ram) (sp : BitVec 64) :
    memLoad (compressionMemory a m sp) (sp - 56) 64 = 1 := by
  unfold compressionMemory
  segment_words []

private theorem compressionMemory_input {a : Registers} {m : Ram} {sp src dst : BitVec 64}
    {key : ByteArray} (call : Call a m sp src dst)
    (outer : (⟨src.toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key 0x5c)) :
    (⟨src.toNat, (keyPad key 0x5c).size⟩ : MemoryRegion).HasBytes
      (compressionMemory a m sp) (keyPad key 0x5c) := by
  refine ⟨rfl, ?_⟩
  intro i
  change (compressionMemory a m sp)[BitVec.ofNat 64 (src.toNat + i.val)]? = _
  have frame := compressionMemory_frame a m call.depth
  have low := call.ctxRead.low
  have above := call.ctxAbove
  have index : i.val < 64 := by simpa only [keyPad_size] using i.isLt
  have hpos : (BitVec.ofNat 64 (src.toNat + i.val)).toNat = src.toNat + i.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bytesEnd : src.toNat + i.val + 1 ≤ src.toNat + 168 := by omega
  have bound : src.toNat + i.val + 1 ≤ 2 ^ 64 :=
    Nat.le_trans bytesEnd (Nat.le_trans low (by decide))
  have separate : Outside [scratch sp] (BitVec.ofNat 64 (src.toNat + i.val)) 1 := by
    refine ⟨by rw [hpos]; exact bound, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change sp.toNat - 704 + 704 ≤ (BitVec.ofNat 64 (src.toNat + i.val)).toNat
    rw [hpos, Nat.sub_add_cancel call.depth]
    omega
  exact (frame.outside _ separate).trans (outer.2 i)

private theorem outsideCompression {sp : BitVec 64} (depth : 704 ≤ sp.toNat)
    (off : BitVec 64) (bound : 8 ≤ off.toNat ∧ off.toNat ≤ 56) :
    Outside (Compression.footprint (sp - 368) (sp - 88)) (sp - off) 8 := by
  have pos : (sp - off).toNat = sp.toNat - off.toNat := BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def]
    omega)
  have stack : (sp - 368).toNat = sp.toNat - 368 := stackAddress depth (by decide)
  have hash : (sp - 88).toNat = sp.toNat - 88 := stackAddress depth (by decide)
  have := sp.isLt
  refine ⟨by rw [pos]; omega, ?_⟩
  intro r hr
  simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right
    dsimp only
    omega
  · right
    dsimp only
    omega

private theorem savedSlotBounds (i : Fin 6) :
    8 ≤ (#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i].toNat ∧
    (#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i].toNat ≤ 56 := by
  finite_cases i <;> decide +kernel

theorem prologue {a : Registers} {m : Ram} {sp src dst : BitVec 64} {key : ByteArray}
    (call : Call a m sp src dst)
    (outer : (⟨src.toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key 0x5c)) :
    ∃ b t, Reaches .l107a50 a m .l107adb b t ∧ Prologue a b m t sp src dst ∧
      Compression.StateAt t (sp - 360 + 272) (compressBlocks initialHash (keyPad key 0x5c)) ∧
      memLoad t (sp - 360 + 304) 64 = 1 := by
  obtain ⟨b, step, rsp, rdi, rsi, rdx, output, hashPtr, input, kept⟩ := setupCompression call
  let t := compressionMemory a m sp
  have depth := call.depth
  have before := compressionMemory_frame a m depth
  have stack : Writable Extracted.programImage t (sp - 704) 704 := call.stack.of_frame before
  have base : (sp - 704).toNat = sp.toNat - 704 := stackAddress depth (by decide)
  have push : (sp - 368).toNat = sp.toNat - 368 := stackAddress depth (by decide)
  have hash : (sp - 88).toNat = sp.toNat - 88 := stackAddress depth (by decide)
  have above := call.ctxAbove
  have tag : memLoad t (sp - 368) 64 = 0x107adb :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have child : Compression.Call b t (sp - 368) (sp - 88) src initialHash (keyPad key 0x5c) := by
    refine ⟨rsp, rdi, rsi, ?_, ?_, compressionMemory_state a m sp, compressionMemory_input call outer,
      ?_, stack.sub (by omega) (by omega), by omega, ?_, stack.readable.sub (by omega) (by omega),
      ?_, Or.inr (by omega), Or.inr (by omega)⟩
    · rw [keyPad_size]
      exact rdx
    · rintro ⟨i, hi⟩ saved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at saved
      rcases saved with rfl | rfl | rfl | rfl | rfl | rfl
      · exact congrArg Value.width output
      · exact (congrArg Value.width (kept 5 (by decide))).trans (call.widths 5 (by decide))
      · exact (congrArg Value.width (kept 12 (by decide))).trans (call.widths 12 (by decide))
      · exact (congrArg Value.width (kept 13 (by decide))).trans (call.widths 13 (by decide))
      · exact congrArg Value.width hashPtr
      · exact congrArg Value.width input
    · rw [keyPad_size]
      exact (call.ctxRead.of_frame before).sub (Nat.le_refl _) (by omega)
    · rw [BitVec.sub_sub]
      change Writable Extracted.programImage t (sp - 704) 336
      exact stack.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide) _)
    · rw [tag]
      decide
  obtain ⟨out, exec, post⟩ := Compression.execute child
  have back := ParseSignature.exec_reaches_resume exec compressResume [] (by rw [post.tag, tag]; rfl)
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [5, 12, 13, 22, 39, 50, 51]) :
      out.values[i] = a[i] := (post.preserved i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega)).trans (kept i hi)
  have within : RegionsWithin (Compression.footprint (sp - 368) (sp - 88)) [scratch sp] := by
    intro r hr
    simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨scratch sp, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · change sp.toNat - 704 ≤ (sp - 368).toNat - 336 ∧
        (sp - 368).toNat - 336 + 336 ≤ sp.toNat - 704 + 704
      rw [push]
      omega
    · change sp.toNat - 704 ≤ (sp - 88).toNat ∧ (sp - 88).toNat + 32 ≤ sp.toNat - 704 + 704
      rw [hash]
      omega
  have writes := before.trans post.writes within
  refine ⟨out.values, out.store, .step (congrArg (Transfer.next _ []) step) back, ?_, ?_, ?_⟩
  · refine ⟨?_, (preserved 22 (by decide)).trans call.df,
      (post.preserved 3 (by decide)).trans output, (post.preserved 15 (by decide)).trans input,
      ?_, ?_, writes, ?_⟩
    · rw [post.rsp]
      congr 1
      bv_omega
    · intro i hi
      have hs : i.val ∈ [3, 5, 12, 13, 14, 15] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega
      rw [post.preserved i (List.mem_append_left [22, 39, 50, 51] hs)]
      exact child.savedWidths i hs
    · intro i hi
      apply preserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    · intro i
      rw [post.writes.memLoad_eq (outsideCompression depth _ (savedSlotBounds i))]
      exact compressionMemory_slots a m sp i
  · rw [show sp - 360 + 272 = sp - 88 by bv_omega]
    exact post.state
  · rw [show sp - 360 + 304 = sp - 56 by bv_omega,
      post.writes.memLoad_eq (outsideCompression depth 56 (by decide))]
    exact compressionMemory_count a m sp

end K256.Proofs.Signing.UpdateV.Finalize
