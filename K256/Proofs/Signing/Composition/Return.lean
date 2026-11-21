import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Signing.Serialize
import K256.Proofs.Signing.LIR.SigningKeyTrySign
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Signing.Composition

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

private theorem successBranch {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4] = ⟨64, base⟩) (load : LoadOk m (base + 72) 4)
    (tag : memLoad m (base + 72) 64 = 0) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l102795, a, m⟩ =
      .jump ⟨.l1027b7, b, m⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 13, 22] → b[i] = a[i]) := by
  have bits : a[4].get 64 = base := congrArg (Value.get 64) rsp
  have low : (memLoad m (base + 72) 64).setWidth 32 = memLoad m (base + 72) 32 := by
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    simpa only [Nat.zero_div, BitVec.add_zero] using
      extractLsb'_memLoad m (base + 72) (n := 64) 0 32 (by decide) (by decide) (by decide)
  have zero : memLoad m (base + 72) 32 = 0 := by rw [← low, tag]; rfl
  refine ⟨?_, ?run, ?kept⟩
  case run =>
    cfg_eval
    simp only [bits, load, zero, cmpSpec_ZF, ↓reduceIte]
    rfl
  case kept =>
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem serializeBlock {code : CodeMap} {a : Registers} {m : Ram} {base dst : BitVec 64}
    (hcode : ∀ x ∈ codeRange 0x1027b7 LIR.bytes_l1027b7, x ∈ code)
    (rsp : a[4] = ⟨64, base⟩) (rbx : a[3] = ⟨64, dst⟩)
    (read : Readable m (base + 80) 64) (write : Writable code m dst 64) :
    ∃ (b : Registers) (n : Ram),
      LIR.program.runBlock (dialect code) ⟨.l1027b7, a, m⟩ = .jump ⟨.l10281c, b, n⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [4, 5, 13, 22] → b[i] = a[i]) ∧
      RamWriteFrame m n [⟨dst.toNat, 64⟩] ∧
      ∀ i < 8, memLoad n (wordAddr dst 64 i) 64 =
        bswapSpec (memLoad m (wordAddr (base + 80) 64 (4 * (i / 4) + (3 - i % 4))) 64) := by
  let words (i : Nat) := bswapSpec (memLoad m
    (base + BitVec.ofNat 64 (80 + 8 * (4 * (i / 4) + (3 - i % 4)))) 64)
  let addr (i : Nat) := if i = 0 then dst else wordAddr dst 64 i
  have addrEq (i : Nat) : addr i = wordAddr dst 64 i := by
    by_cases hi : i = 0
    · subst i
      exact (BitVec.add_zero dst).symm
    · simp only [addr, hi, ite_false]
  let writeWords : Nat → Ram := fun n => Nat.rec m
    (fun i acc => memStore acc (addr i) (words i)) n
  have low := write.readable.low
  have addrNat (i : Nat) (hi : i < 8) : (wordAddr dst 64 i).toNat = dst.toNat + 8 * i := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
  have frame (n : Nat) (hn : n ≤ 8) : RamWriteFrame m (writeWords n) [⟨dst.toNat, 64⟩] := by
    induction n with
    | zero => exact .refl _ _
    | succ n ih =>
      apply (ih (by omega)).memStore
      refine ⟨⟨dst.toNat, 64⟩, List.mem_singleton_self _, ?_⟩
      change dst.toNat ≤ (addr n).toNat ∧
        (addr n).toNat + 8 ≤ dst.toNat + 64 ∧ (addr n).toNat + 8 ≤ 2 ^ 64
      rw [addrEq, addrNat n (by omega)]
      omega
  have written (n : Nat) (hn : n ≤ 8) (i : Nat) (hi : i < n) :
      memLoad (writeWords n) (wordAddr dst 64 i) 64 = words i := by
    induction n with
    | zero => omega
    | succ n ih =>
      change memLoad (memStore (writeWords n) (addr n) (words n))
        (wordAddr dst 64 i) 64 = words i
      rw [addrEq]
      by_cases he : i = n
      · subst i
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_toNat <;>
            simp only [addrNat n (by omega), addrNat i (by omega), Nat.reduceDiv] <;> omega)]
        exact ih (by omega) (by omega)
  have load (off : Nat) (hoff : off + 8 ≤ 64) :
      LoadOk m (base + BitVec.ofNat 64 (80 + off)) 8 := by
    apply LoadOk.of_offsets read rfl rfl
    have eq : BitVec.ofNat 64 (80 + off) - 80 = BitVec.ofNat 64 off := by
      rw [BitVec.ofNat_add]
      bv_omega
    rw [eq]
    change off % (2^64) + 8 ≤ 64
    omega
  have store (i off len : Nat) (hi : i < 8) (hoff : off + len ≤ LIR.bytes_l1027b7.length) :
      StoreOk code (writeWords i) (addr i) 8 (0x1027b7 + BitVec.ofNat 64 off) len := by
    rw [addrEq]
    have w : Writable code (writeWords i) (wordAddr dst 64 i) 8 :=
      (write.of_frame (frame i (by omega))).sub (by rw [addrNat i hi]; omega) (by rw [addrNat i hi]; omega)
    exact ParseSignature.storeOk_of_codeRange w hcode hoff
  have rspBits : a[4].get 64 = base := congrArg (Value.get 64) rsp
  have rbxBits : a[3].get 64 = dst := congrArg (Value.get 64) rbx
  refine ⟨?_, writeWords 8, ?run, ?post⟩
  case run =>
    cfg_eval [LIR.b_l1027b7_1, rspBits, rbxBits]
    refine (ite_eq_left (load 24 (by decide))).trans ?_
    refine (ite_eq_left (load 16 (by decide))).trans ?_
    refine (ite_eq_left (load 0 (by decide))).trans ?_
    refine (ite_eq_left (load 8 (by decide))).trans ?_
    refine (ite_eq_left (load 56 (by decide))).trans ?_
    refine (ite_eq_left (load 48 (by decide))).trans ?_
    refine (ite_eq_left (load 40 (by decide))).trans ?_
    refine (ite_eq_left (load 32 (by decide))).trans ?_
    refine (ite_eq_left (store 0 70 3 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 1 73 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 2 77 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 3 81 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 4 85 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 5 89 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 6 93 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (store 7 97 4 (by decide) (by decide))).trans ?_
    rfl
  case post =>
    refine ⟨?_, frame 8 (by decide), ?_⟩
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · intro i hi
      rw [written 8 (by decide) i hi]
      dsimp only [words, wordAddr, Nat.reduceDiv]
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl

private abbrev cleanup (base : BitVec 64) : MemoryRegion := ⟨(base + 72).toNat, 160⟩

set_option maxHeartbeats 650000 in
private theorem epilogue {a : Registers} {m : Ram} {base ret : BitVec 64}
    (rsp : a[4] = ⟨64, base⟩)
    (window : Writable Extracted.programImage m base 480)
    (retWord : memLoad m (base + 472) 64 = ret) (retLow : ret.toNat < 2^32) :
    ∃ (out : Output Value Ram Reg.count),
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l10281c, a, m⟩ = .returned out ∧
      RamWriteFrame m out.store [cleanup base] ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, base + 480⟩ ∧
      out.values[3] = ⟨64, memLoad m (base + 440) 64⟩ ∧
      out.values[12] = ⟨64, memLoad m (base + 448) 64⟩ ∧
      out.values[14] = ⟨64, memLoad m (base + 456) 64⟩ ∧
      out.values[15] = ⟨64, memLoad m (base + 464) 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5, 13, 22] → out.values[i] = a[i]) ∧
      out.values[0].width = 64 := by
  have rspBits : a[4].get 64 = base := congrArg (Value.get 64) rsp
  have addrNat {off : Nat} (h : off ≤ 480) :
      (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    have low := window.readable.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have keep {n : Ram} (frame : RamWriteFrame m n [cleanup base]) (off : Nat)
      (after : 232 ≤ off) (within : off + 8 ≤ 480) :
      memLoad n (base + BitVec.ofNat 64 off) 64 =
      memLoad m (base + BitVec.ofNat 64 off) 64 := by
    apply frame.memLoad_eq
    have low := window.readable.low
    refine ⟨by rw [addrNat (by omega)]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (base + 72).toNat + 160 ≤ (base + BitVec.ofNat 64 off).toNat
    rw [show (base + 72).toNat = base.toNat + 72 from addrNat (by decide), addrNat (by omega)]
    omega
  have inCleanup {off : Nat} (lo : 72 ≤ off) (hi : off + 8 ≤ 232) :
      InRegions [cleanup base] (base + BitVec.ofNat 64 off) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (base + 72).toNat ≤ _ ∧ _ + 8 ≤ (base + 72).toNat + 160 ∧ _
    have low := window.readable.low
    rw [addrNat (by omega), show (base + 72).toNat = base.toNat + 72 from addrNat (by decide)]
    omega
  have read {n : Ram} (frame : RamWriteFrame m n [cleanup base]) (off : Nat)
      (bound : off + 8 ≤ 480) : LoadOk n (base + BitVec.ofNat 64 off) 8 :=
    LoadOk.of_region (window.readable.of_frame frame) (by rw [addrNat (by omega)]; omega)
      (by rw [addrNat (by omega)]; omega)
  have included := fun x hx => Common.fnCode_subset_programImage x (LIR.code_l10281c x hx)
  have store {n : Ram} (frame : RamWriteFrame m n [cleanup base]) (off pc len : Nat)
      (bound : off + 8 ≤ 480) (within : pc + len ≤ LIR.bytes_l10281c.length) :
      StoreOk Extracted.programImage n (base + BitVec.ofNat 64 off) 8
        (0x10281c + BitVec.ofNat 64 pc) len := by
    apply ParseSignature.storeOk_of_codeRange _ included within
    exact (window.of_frame frame).sub (by rw [addrNat (by omega)]; omega)
      (by rw [addrNat (by omega)]; omega)
  let m1 := memStore m (base + 72) (0 : BitVec 64)
  let m2 := memStore m1 (base + 80) (0 : BitVec 64)
  let m3 := memStore m2 (base + 88) (0 : BitVec 64)
  let m4 := memStore m3 (base + 96) (0 : BitVec 64)
  let m5 := memStore m4 (base + 200) (memLoad m4 (base + 72) 64)
  let m6 := memStore m5 (base + 208) (memLoad m5 (base + 80) 64)
  let m7 := memStore m6 (base + 216) (memLoad m6 (base + 88) 64)
  let m8 := memStore m7 (base + 224) (memLoad m7 (base + 96) 64)
  have f0 : RamWriteFrame m m [cleanup base] := .refl _ _
  have f1 : RamWriteFrame m m1 [cleanup base] := f0.memStore _ (inCleanup (by decide) (by decide))
  have f2 : RamWriteFrame m m2 [cleanup base] := f1.memStore _ (inCleanup (by decide) (by decide))
  have f3 : RamWriteFrame m m3 [cleanup base] := f2.memStore _ (inCleanup (by decide) (by decide))
  have f4 : RamWriteFrame m m4 [cleanup base] := f3.memStore _ (inCleanup (by decide) (by decide))
  have f5 : RamWriteFrame m m5 [cleanup base] := f4.memStore _ (inCleanup (by decide) (by decide))
  have f6 : RamWriteFrame m m6 [cleanup base] := f5.memStore _ (inCleanup (by decide) (by decide))
  have f7 : RamWriteFrame m m7 [cleanup base] := f6.memStore _ (inCleanup (by decide) (by decide))
  have f8 : RamWriteFrame m m8 [cleanup base] := f7.memStore _ (inCleanup (by decide) (by decide))
  have fold1 : memStore m (base + 72) (0 : BitVec 64) = m1 := rfl
  have fold2 : memStore m1 (base + 80) (0 : BitVec 64) = m2 := rfl
  have fold3 : memStore m2 (base + 88) (0 : BitVec 64) = m3 := rfl
  have fold4 : memStore m3 (base + 96) (0 : BitVec 64) = m4 := rfl
  have fold5 : memStore m4 (base + 200) (memLoad m4 (base + 72) 64) = m5 := rfl
  have fold6 : memStore m5 (base + 208) (memLoad m5 (base + 80) 64) = m6 := rfl
  have fold7 : memStore m6 (base + 216) (memLoad m6 (base + 88) 64) = m7 := rfl
  have fold8 : memStore m7 (base + 224) (memLoad m7 (base + 96) 64) = m8 := rfl
  have st0 := store f0 72 0 9 (by decide) (by decide)
  have st1 := store f1 80 9 9 (by decide) (by decide)
  have st2 := store f2 88 18 9 (by decide) (by decide)
  have st3 := store f3 96 27 9 (by decide) (by decide)
  have st4 := store f4 200 41 8 (by decide) (by decide)
  have st5 := store f5 208 54 8 (by decide) (by decide)
  have st6 := store f6 216 67 8 (by decide) (by decide)
  have st7 := store f7 224 80 8 (by decide) (by decide)
  have rd4 := read f4 72 (by decide)
  have rd5 := read f5 80 (by decide)
  have rd6 := read f6 88 (by decide)
  have rd7 := read f7 96 (by decide)
  have pop3 := read f8 440 (by decide)
  have pop12 := read f8 448 (by decide)
  have pop14 := read f8 456 (by decide)
  have pop15 := read f8 464 (by decide)
  have retRead := read f8 472 (by decide)
  have retFinal : memLoad m8 (base + 472) 64 = ret := (keep f8 472 (by decide) (by decide)).trans retWord
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rspBits, BitVec.add_assoc, retFinal, retLow,
      fold1, fold2, fold3, fold4, fold5, fold6, fold7, fold8, and_self]
    refine (ite_eq_left st0).trans ?_
    refine (ite_eq_left st1).trans ?_
    refine (ite_eq_left st2).trans ?_
    refine (ite_eq_left st3).trans ?_
    refine (ite_eq_left rd4).trans ?_
    refine (ite_eq_left st4).trans ?_
    refine (ite_eq_left rd5).trans ?_
    refine (ite_eq_left st5).trans ?_
    refine (ite_eq_left rd6).trans ?_
    refine (ite_eq_left st6).trans ?_
    refine (ite_eq_left rd7).trans ?_
    refine (ite_eq_left st7).trans ?_
    refine (ite_eq_left pop3).trans ?_
    refine (ite_eq_left pop12).trans ?_
    refine (ite_eq_left pop14).trans ?_
    refine (ite_eq_left pop15).trans ?_
    refine (ite_eq_left retRead).trans ?_
    rfl
  case post =>
    refine ⟨f8, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · exact congrArg (fun w => (⟨64, w⟩ : Value)) (keep f8 440 (by decide) (by decide))
    · exact congrArg (fun w => (⟨64, w⟩ : Value)) (keep f8 448 (by decide) (by decide))
    · exact congrArg (fun w => (⟨64, w⟩ : Value)) (keep f8 456 (by decide) (by decide))
    · exact congrArg (fun w => (⟨64, w⟩ : Value)) (keep f8 464 (by decide) (by decide))
    · rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> rfl

theorem returnSignature {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret, msg])
    {a : Registers} {m : Ram} {pair : Nat × Nat} (result : Result s pair a m) :
    ∃ out, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l102795, a, m⟩, []⟩ out ∧
      signatureOutput s pair out := by
  let base := stackPtr s - 472
  let dst := s.regValue .rdi
  let stack := Stack.region s signingKeyTrySign.minStackBytes
  let dest := outputRegion signingKeyTrySign s
  have mem := result.toMemory
  have rsp : a[4] = ⟨64, base⟩ := by
    exact result.rsp.trans (congrArg (fun w => (⟨64, w⟩ : Value)) (by dsimp only [sp, base]; bv_omega))
  have stackEq := stackRegion call
  have room := (stackBounds call).1
  have low := (stackBounds call).2.1
  have bottom : (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have baseNat : base.toNat = (stackPtr s).toNat - 472 :=
    Common.stackOffset (off := 472) call.stackAvailable (by decide)
  have disp (off : Nat) (h : off ≤ 480) : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have sep : dest.Disjoint stack := (List.pairwise_cons.mp call.separation.1).1 _ List.mem_cons_self
  have apart : dst.toNat + 64 ≤ (stackPtr s).toNat - 11192 ∨
      (stackPtr s).toNat + 8 ≤ dst.toNat := by
    have bound := apart_of_disjoint sep (by change 0 < 64; decide : 0 < dest.size)
      (by rw [show stack = _ from stackEq]; change 0 < 11200; decide : 0 < stack.size)
    change dest.start + dest.size ≤ stack.start ∨ stack.start + stack.size ≤ dest.start at bound
    rw [show stack = _ from stackEq] at bound
    change dst.toNat + 64 ≤ (stackPtr s - 11192).toNat ∨
      (stackPtr s - 11192).toNat + 11200 ≤ dst.toNat at bound
    rw [bottom] at bound
    omega
  have tagAddr : base + 72 = sp s + 888 := by dsimp only [base, sp]; bv_omega
  have rAddr : base + 80 = sp s + 896 := by dsimp only [base, sp]; bv_omega
  have sAddr : base + 80 + 32 = sp s + 928 := by dsimp only [base, sp]; bv_omega
  have window : Writable Extracted.programImage m base 480 :=
    (mem.window call).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have tagLoad : LoadOk m (base + 72) 4 :=
    LoadOk.of_offsets window.readable rfl (addr_self _) (by decide)
  have tagWord : memLoad m (base + 72) 64 = 0 := by rw [tagAddr]; exact result.tag
  obtain ⟨b, branch, branchKept⟩ := successBranch rsp tagLoad tagWord
  have dstWrite : Writable Extracted.programImage m dst 64 :=
    (Common.outputWritable call rfl (by decide)).of_frame mem.written
  obtain ⟨c, n, serialized, serializeKept, stores, words⟩ := serializeBlock
    (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l1027b7 x hx))
    ((branchKept 4 (by decide)).trans rsp) ((branchKept 3 (by decide)).trans result.dst)
    (window.readable.of_offsets rfl (addr_self _) (by decide)) dstWrite
  have kept (i : Fin Reg.count) (h : i.val ∈ [4, 5, 13, 22]) : c[i] = a[i] :=
    (serializeKept i h).trans (branchKept i (.tail 3 h))
  have bytes : dest.HasBytes n (K256.Spec.Ecdsa.normalizeS pair.1 pair.2) := by
    apply normalizedBytes_of_serialization (src := base + 80) ?_ ?_
      (dstWrite.readable.of_frame stores) words
    · rw [rAddr]; exact result.r
    · rw [sAddr]; exact result.lowS
  have save (addr : BitVec 64) (off : Nat) (eq : addr = base + BitVec.ofNat 64 off)
      (lo : 440 ≤ off) (hi : off + 8 ≤ 480) : memLoad n addr 64 = memLoad m addr 64 := by
    subst addr
    apply stores.memLoad_eq
    refine ⟨by rw [disp off (by omega)]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (base + BitVec.ofNat 64 off).toNat + 8 ≤ dst.toNat ∨
      dst.toNat + 64 ≤ (base + BitVec.ofNat 64 off).toNat
    rw [disp off (by omega)]
    rcases apart with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have retAddr : base + 472 = stackPtr s := by dsimp only [base]; bv_omega
  have retWord : memLoad n (base + 472) 64 = (returnBoundary s).rip := by
    rw [save (base + 472) 472 rfl (by decide) (by decide), retAddr]
    exact mem.ret
  obtain ⟨ret, slot, retLow, _⟩ := call.returnAddress
  have boundaryLow : (returnBoundary s).rip.toNat < 2^32 := by
    rw [show (returnBoundary s).rip = ret from memLoad_returnSlot slot]
    exact retLow
  obtain ⟨out, step, clean, tag, restored, bx, r12, r14, r15, preserved, status⟩ :=
    epilogue ((kept 4 (by decide)).trans rsp) (window.of_frame stores) retWord boundaryLow
  have cleanStart : (cleanup base).start = base.toNat + 72 := disp 72 (by decide)
  have cleanInside : stack.start ≤ (cleanup base).start ∧
      (cleanup base).start + (cleanup base).size ≤ stack.start + stack.size := by
    rw [cleanStart, show stack = _ from stackEq]
    change (stackPtr s - 11192).toNat ≤ base.toNat + 72 ∧
      base.toNat + 72 + 160 ≤ (stackPtr s - 11192).toNat + 11200
    rw [bottom]
    omega
  have frame := (RamWriteFrame.refl s.external [dest, stack]).trans mem.written (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨stack, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have frame := frame.trans stores (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨dest, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have frame := frame.trans clean (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨stack, List.mem_cons_of_mem _ List.mem_cons_self, cleanInside⟩)
  have resultBytes : dest.HasBytes out.store (K256.Spec.Ecdsa.normalizeS pair.1 pair.2) := by
    refine ⟨bytes.1, fun i => ?_⟩
    have len : (K256.Spec.Ecdsa.normalizeS pair.1 pair.2).size = 64 := bytes.1
    have bound := dstWrite.readable.low
    have idx := i.isLt
    rw [clean.outside _ ?_]
    · exact bytes.2 i
    · change Outside _ (BitVec.ofNat 64 (dst.toNat + i.val)) 1
      have byteAddr : (BitVec.ofNat 64 (dst.toNat + i.val)).toNat = dst.toNat + i.val :=
        Nat.mod_eq_of_lt (by omega)
      refine ⟨by rw [byteAddr]; omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      change _ ≤ (cleanup base).start ∨ (cleanup base).start + 160 ≤ _
      rw [cleanStart, byteAddr]
      rcases apart with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  refine ⟨out, .next (congrArg (Transfer.next _ []) branch)
    (.next (congrArg (Transfer.next _ []) serialized) (.done (congrArg (Transfer.next _ []) step))),
    ⟨tag, ?_, ?_, ?_, frame, status⟩, resultBytes⟩
  · exact restored.trans (congrArg (fun w => (⟨64, w⟩ : Value)) (by
      change base + 480 = stackPtr s + 8
      dsimp only [base]
      bv_omega))
  · exact (preserved 22 (by decide)).trans ((kept 22 (by decide)).trans result.df)
  · have b3 : base + 440 = stackPtr s - 32 := by dsimp only [base]; bv_omega
    have b12 : base + 448 = stackPtr s - 24 := by dsimp only [base]; bv_omega
    have b14 : base + 456 = stackPtr s - 16 := by dsimp only [base]; bv_omega
    have b15 : base + 464 = stackPtr s - 8 := by dsimp only [base]; bv_omega
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · change out.values[3] = ⟨64, s.regValue .rbx⟩
      rw [bx, save (base + 440) 440 rfl (by decide) (by decide), b3, mem.savedWrapperRBX]
    · exact (preserved 5 (by decide)).trans ((kept 5 (by decide)).trans result.rbp)
    · change out.values[12] = ⟨64, s.regValue .r12⟩
      rw [r12, save (base + 448) 448 rfl (by decide) (by decide), b12, mem.savedWrapperR12]
    · exact (preserved 13 (by decide)).trans ((kept 13 (by decide)).trans result.r13)
    · change out.values[14] = ⟨64, s.regValue .r14⟩
      rw [r14, save (base + 456) 456 rfl (by decide) (by decide), b14, mem.savedWrapperR14]
    · change out.values[15] = ⟨64, s.regValue .r15⟩
      rw [r15, save (base + 464) 464 rfl (by decide) (by decide), b15, mem.savedWrapperR15]

end K256.Proofs.Signing.Composition
