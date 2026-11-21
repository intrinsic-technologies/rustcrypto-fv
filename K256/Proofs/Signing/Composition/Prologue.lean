import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

private def prologueMemory (a : Registers) (m : Ram) (p : BitVec 64) : Ram :=
  let m := memStore m (p + 800) (a[5].get 64)
  let m := memStore m (p + 792) (a[15].get 64)
  let m := memStore m (p + 784) (a[14].get 64)
  let m := memStore m (p + 776) (a[13].get 64)
  let m := memStore m (p + 768) (a[12].get 64)
  let m := memStore m (p + 760) (a[3].get 64)
  let m := memStore m (p + 344) (a[6].get 64)
  let m := memStore m (p + 416) (a[7].get 64)
  let m := memStore m (p + 576) (0x5be0cd191f83d9ab : BitVec 64)
  let m := memStore m (p + 568) (0x9b05688c510e527f : BitVec 64)
  let m := memStore m (p + 560) (0xa54ff53a3c6ef372 : BitVec 64)
  let m := memStore m (p + 552) (0xbb67ae856a09e667 : BitVec 64)
  let m := memStore m (p + 584) (0 : BitVec 64)
  memStore m (p + 551) (0 : BitVec 8)

private theorem prologueBlock {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p + 808) (count : a[1].get 64 = 1)
    (win : Writable Extracted.programImage m p 808) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105420, a, m⟩ =
      .jump ⟨.l1054a6, b, prologueMemory a m p⟩ ∧
      b[4] = ⟨64, p⟩ ∧ b[1] = a[1] ∧ b[2] = a[2] ∧ b[22] = a[22] ∧
      b[39] = a[39] ∧ b[50] = a[50] ∧ b[51] = a[51] := by
  have addr (off : BitVec 64) : a[4].get 64 - off = p + (808 - off) := by
    rw [rsp]
    bv_omega
  have slot (off : BitVec 64) (n : Nat) (h : off.toNat + n ≤ 808) :
      Writable Extracted.programImage m (p + off) n :=
    win.of_offsets rfl (addr_self p) (by
      change (off - 0#64).toNat + n ≤ 808
      simpa only [BitVec.sub_zero] using h)
  have guard {mem : Ram} {dst pc : BitVec 64} {n len : Nat}
      (h : Writable Extracted.programImage mem dst n)
      (inside : (pc - 0x105420).toNat + len ≤ LIR.bytes_l105420.length) :
      StoreOk Extracted.programImage mem dst n pc len := by
    have h' := ParseSignature.storeOk_of_codeRange h
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l105420 x hx)) inside
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show 0x105420 + (pc - 0x105420) = pc by bv_omega] at h'
  refine ⟨?regs, ?run, ?kept⟩
  case run =>
    cfg_eval
    simp only [addr, BitVec.reduceSub, BitVec.add_zero, count]
    iterate 14
      refine Eq.trans (ite_eq_left ?_) ?_
      apply guard _ (by decide +kernel)
      repeat' apply Writable.memStore
      exact slot _ _ (by decide)
    rfl
  case kept => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


private theorem stackSlotToNat (p : BitVec 64) (low : p.toNat + 1296 ≤ 2^32)
    (off : Nat) (bound : off ≤ 1296) :
    (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem prologueMemory_frame {a : Registers} {m : Ram} {p : BitVec 64}
    (low : p.toNat + 1296 ≤ 2^32) :
    RamWriteFrame m (prologueMemory a m p) [⟨p.toNat, 808⟩] := by
  have slot (off wid : Nat) (bound : off + wid ≤ 808) :
      InRegions [⟨p.toNat, 808⟩] (p + BitVec.ofNat 64 off) wid := by
    refine ⟨_, .head _, ?_⟩
    change p.toNat ≤ _ ∧ _ + _ ≤ p.toNat + 808 ∧ _ + _ ≤ 2^64
    rw [stackSlotToNat p low off (by omega)]
    omega
  unfold prologueMemory
  iterate 14
    apply RamWriteFrame.memStore _ _ (slot _ _ (by decide))
  exact .refl _ _

private theorem prologueMemory_words (a : Registers) (m : Ram) (p : BitVec 64) :
    let n := prologueMemory a m p
    memLoad n (p + 344) 64 = a[6].get 64 ∧
    memLoad n (p + 416) 64 = a[7].get 64 ∧
    memLoad n (p + 760) 64 = a[3].get 64 ∧
    memLoad n (p + 776) 64 = a[13].get 64 ∧
    memLoad n (p + 800) 64 = a[5].get 64 ∧
    memLoad n (p + 552) 64 = 0xbb67ae856a09e667 ∧
    memLoad n (p + 560) 64 = 0xa54ff53a3c6ef372 ∧
    memLoad n (p + 568) 64 = 0x9b05688c510e527f ∧
    memLoad n (p + 576) 64 = 0x5be0cd191f83d9ab ∧
    memLoad n (p + 551) 8 = 0 ∧
    memLoad n (p + 584) 64 = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
      only [prologueMemory, memLoad_memStore_same, memLoad_memStore_of_rangeApart]

private theorem prologueInitialHash {m : Ram} {p : BitVec 64}
    (word0 : memLoad m (p + 552) 64 = 0xbb67ae856a09e667)
    (word1 : memLoad m (p + 560) 64 = 0xa54ff53a3c6ef372)
    (word2 : memLoad m (p + 568) 64 = 0x9b05688c510e527f)
    (word3 : memLoad m (p + 576) 64 = 0x5be0cd191f83d9ab) :
    Verify.Hash.Compression.StateAt m (p + 552) Verify.Hash.initialHash := by
  have half {off : Nat} {v : BitVec 64} (k : Nat) (hk : k ≤ 1)
      (w : memLoad m (p + BitVec.ofNat 64 off) 64 = v) :
      memLoad m (p + BitVec.ofNat 64 (off + 4 * k)) 32 = v.extractLsb' (32 * k) 32 := by
    have h := extractLsb'_memLoad m (p + BitVec.ofNat 64 off)
      (n := 64) (32 * k) 32 (by omega) (by decide) (by omega)
    rw [w, show 32 * k / 8 = 4 * k by omega, BitVec.add_assoc, ← BitVec.ofNat_add] at h
    exact h.symm
  have words :
      (Vector.ofFn fun i : Fin 8 => Verify.Hash.initialHash[i.val]!.toBitVec) =
        Standards.NIST.SHA2.SHA256.«H⁽⁰⁾» := by decide +kernel
  refine ⟨by decide +kernel, ?_⟩
  rw [words]
  intro i hi
  have addr : wordAddr (p + 552) 32 i = p + BitVec.ofNat 64 (552 + 4 * i) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [addr]
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact half (off := 552) 0 (by decide) word0
  · exact half (off := 552) 1 (by decide) word0
  · exact half (off := 560) 0 (by decide) word1
  · exact half (off := 560) 1 (by decide) word1
  · exact half (off := 568) 0 (by decide) word2
  · exact half (off := 568) 1 (by decide) word2
  · exact half (off := 576) 0 (by decide) word3
  · exact half (off := 576) 1 (by decide) word3

private theorem registerBits {x : Value} {bits : BitVec 64} (eq : x = ⟨64, bits⟩) :
    x.get 64 = bits := by
  subst x
  rfl

theorem prologue {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} (entry : CoreEntry s d msg a m) :
    ∃ b n, Reach (core .l105420 a m) (core .l1054a6 b n) ∧ HashEntry s d msg b n := by
  obtain ⟨depth, top, base⟩ := stackBounds call
  have low : (sp s).toNat + 1296 ≤ 2^32 := by omega
  have bottom : (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have win := (entry.toKeyMemory.toMemory.window call).sub (a := sp s) (n := 808)
    (by omega) (by omega)
  have startRsp : a[4].get 64 = sp s + 808 := registerBits entry.rsp
  have startCount : a[1].get 64 = 1 := registerBits entry.count
  obtain ⟨b, run, rsp, count, descriptor, df, mxcsr, ftw, fcw⟩ := prologueBlock startRsp startCount win
  let n := prologueMemory a m (sp s)
  have frame : RamWriteFrame m n [⟨(sp s).toNat, 808⟩] := prologueMemory_frame low
  have keep (off : Nat) (lower : 808 ≤ off) (upper : off + 8 ≤ 1296) :
      memLoad n (sp s + BitVec.ofNat 64 off) 64 = memLoad m (sp s + BitVec.ofNat 64 off) 64 := by
    apply frame.memLoad_eq
    rw [Outside, stackSlotToNat _ low off (by omega)]
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (sp s).toNat + 808 ≤ _; omega)
  have stackWord (off : Nat) (bound : off ≤ 1288) :
      stackPtr s - BitVec.ofNat 64 off = sp s + BitVec.ofNat 64 (1288 - off) := by
    have sum : BitVec.ofNat 64 off + BitVec.ofNat 64 (1288 - off) = 1288 := by
      rw [← BitVec.ofNat_add, show off + (1288 - off) = 1288 by omega]
      rfl
    unfold sp
    bv_omega
  have written := entry.written.trans frame (by
    rw [stackRegion call]
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, .head _, by change (stackPtr s - 11192).toNat ≤ (sp s).toNat; omega,
      by change (sp s).toNat + 808 ≤ (stackPtr s - 11192).toNat + 11200; omega⟩)
  have keepWrapper (off : Nat) (bound : off ≤ 32) :
      memLoad n (stackPtr s - BitVec.ofNat 64 off) 64 =
        memLoad m (stackPtr s - BitVec.ofNat 64 off) 64 := by
    rw [stackWord off (by omega)]
    exact keep _ (by omega) (by omega)
  have memory : Memory s n :=
    ⟨written,
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using keepWrapper 0 (by decide) :
        memLoad n (stackPtr s) 64 = memLoad m (stackPtr s) 64).trans entry.ret,
      (keepWrapper 32 (by decide)).trans entry.savedWrapperRBX,
      (keepWrapper 24 (by decide)).trans entry.savedWrapperR12,
      (keepWrapper 16 (by decide)).trans entry.savedWrapperR14,
      (keepWrapper 8 (by decide)).trans entry.savedWrapperR15⟩
  have key : KeyMemory s d n := by
    refine ⟨memory, ?_, (keep 808 (by decide) (by decide)).trans entry.coreReturn⟩
    intro i hi
    have addr : wordAddr (sp s + 1016) 64 i = sp s + BitVec.ofNat 64 (1016 + 8 * i) := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    rw [addr, keep _ (by omega) (by omega), ← addr]
    exact entry.key i hi
  obtain ⟨keyPtr, resultPtr, savedOutput, saved13, savedBp, h0, h1, h2, h3, buffered, blocks⟩ :=
    prologueMemory_words a m (sp s)
  refine ⟨b, n, .single ?_, ?_⟩
  · change (LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105420, a, m⟩).next
      _ [resume .l102795 0x102795] = _
    rw [run]
    rfl
  · exact
      { toCoreMemory :=
          { toKeyMemory := key
            keyPtr := keyPtr.trans (registerBits entry.secret)
            resultPtr := resultPtr.trans (registerBits entry.dst)
            savedOutput := savedOutput.trans (registerBits entry.output)
            savedR13 := saved13.trans (registerBits entry.r13)
            savedRbp := savedBp.trans (registerBits entry.framePtr) }
        toDescriptor :=
          ⟨(keep 1136 (by decide) (by decide)).trans entry.pointer,
            (keep 1144 (by decide) (by decide)).trans entry.size⟩
        rsp := rsp
        df := df.trans entry.df
        count := count.trans entry.count
        descriptor := descriptor.trans entry.descriptor
        fp := ⟨(congrArg Value.width mxcsr).trans entry.fp.1,
          (congrArg Value.width ftw).trans entry.fp.2.1,
          (congrArg Value.width fcw).trans entry.fp.2.2⟩
        iv := prologueInitialHash h0 h1 h2 h3
        buffered := buffered
        blocks := blocks }

end K256.Proofs.Signing.Composition
