import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.State
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)
open Encode

private def entryMemory (fr : Activation) : Ram :=
  let m := memStore fr.original (fr.rsp - 8) fr.rbp
  let m := memStore m (fr.rsp - 16) fr.r15
  let m := memStore m (fr.rsp - 24) fr.r14
  let m := memStore m (fr.rsp - 32) fr.r13
  let m := memStore m (fr.rsp - 40) fr.r12
  let m := memStore m (fr.rsp - 48) fr.rbx
  let m := memStore m (fr.rsp - 57) (1#8)
  let m := memStore m (fr.rsp - 57) (0#8)
  let m := memStore m (fr.rsp - 57) (0#8)
  memStore m (fr.rsp - 57) (0#8)

private theorem entryMemory_writes {fr : Activation} (depth : 208 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 208) (extra : List MemoryRegion) :
    RamWriteFrame fr.original (entryMemory fr) (fr.region :: extra) := by
  have pos : fr.low.toNat = fr.rsp.toNat - 208 := by
    rw [low, BitVec.toNat_sub_of_le (by exact depth)]
    rfl
  have slot (off : BitVec 64) (n : Nat) (h : n ≤ off.toNat ∧ off.toNat ≤ 208) :
      InRegions (fr.region :: extra) (fr.rsp - off) n := by
    refine ⟨fr.region, .head _, ?_⟩
    change fr.low.toNat ≤ (fr.rsp - off).toNat ∧
      (fr.rsp - off).toNat + n ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧
      (fr.rsp - off).toNat + n ≤ 2^64
    rw [BitVec.toNat_sub_of_le (by exact Nat.le_trans h.2 depth), pos]
    have := fr.rsp.isLt
    omega
  unfold entryMemory
  iterate 10 apply RamWriteFrame.memStore _ _ (slot _ _ (by decide))
  exact .refl _ _

set_option maxHeartbeats 1500000 in
private theorem orderLength {fr : Activation} {a : Verify.Core.Registers}
    (entry : Atom.All Extracted.programImage a fr.original (Fn100000.frameAt .l100000 fr))
    (depth : 208 ≤ fr.rsp.toNat) (orderAfter : fr.rsp.toNat ≤ fr.rsi.toNat)
    (len : fr.rcx = 32)
    (orderRead : Readable fr.original fr.rsi 32)
    (orderWords : WordsAt fr.original fr.rsi 64 (scalarWords Secp256k1.domain.n)) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l100000, a, fr.original⟩ =
      .jump ⟨.l1000cf, b, entryMemory fr⟩ ∧
      b[0] = ⟨64, 263⟩ ∧ b[2] = ⟨64, 32⟩ ∧ b[4] = ⟨64, fr.rsp - 72⟩ ∧
      b[12] = ⟨64, fr.rdx⟩ ∧ ParseSignature.ArgumentWidths b ∧
      ∀ i : Fin Reg.count, i.val ∈ [7, 22, 39, 50, 51] → b[i] = a[i] := by
  simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, _, cx, dx, bx, bp, si, rdi, _, _, r12, r13, r14, r15, _, _, _, _, _, _, stack, _⟩ := entry
  have rsp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have rcx : a[1].get 64 = 32 := (congrArg (Value.get 64) cx).trans len
  have rsi : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have w2 : a[2].get 64 = fr.rdx := congrArg (Value.get 64) dx
  have w3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have w5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have w12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have w13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have w14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have w15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have orderTop := orderRead.low
  have limb0 : memLoad fr.original fr.rsi 64 = 0xbfd25e8cd0364141 := by
    have h := orderWords 0 (by decide)
    change memLoad fr.original (fr.rsi + 0#64) 64 = 0xbfd25e8cd0364141 at h
    rwa [BitVec.add_zero] at h
  have limb1 : memLoad fr.original (fr.rsi + 8) 64 = 0xbaaedce6af48a03b := orderWords 1 (by decide)
  have limb2 : memLoad fr.original (fr.rsi + 16) 64 = 0xfffffffffffffffe := orderWords 2 (by decide)
  have limb3 : memLoad fr.original (fr.rsi + 24) 64 = 0xffffffffffffffff := orderWords 3 (by decide)
  have inc : ∀ v ∈ codeRange 0x100000 bytes_l100000, v ∈ Extracted.programImage :=
    fun v hv => Common.fnCode_subset_programImage v (code_l100000 v hv)
  have localSlot (d : BitVec 64) (n : Nat) (hd : n ≤ d.toNat ∧ d.toNat ≤ 208) :
      Writable Extracted.programImage fr.original (fr.rsp - d) n := by
    apply stack.sub <;> bv_omega
  have srcSlot (d : BitVec 64) (hd : d.toNat ≤ 24) :
      Readable fr.original (fr.rsi + d) 8 := by
    have addr : (fr.rsi + d).toNat = fr.rsi.toNat + d.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact orderRead.sub (by rw [addr]; omega) (by rw [addr]; omega)
  have srcBase : Readable fr.original fr.rsi 8 :=
    orderRead.sub (Nat.le_refl _) (by omega)
  have guardStore {m : Ram} {addr pc : BitVec 64} {size len : Nat}
      (h : Writable Extracted.programImage m addr size)
      (within : (pc - 0x100000).toNat + len ≤ bytes_l100000.length) :
      StoreOk Extracted.programImage m addr size pc len := by
    have h' := ParseSignature.storeOk_of_codeRange h inc within
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show 0x100000 + (pc - 0x100000) = pc by bv_omega] at h'
  refine ⟨?_, ?run, ?regs⟩
  case run =>
    cfg_eval
    simp only [rsp, rcx, rsi, w2, w3, w5, w12, w13, w14, w15]
    segment_words [limb0, limb1, limb2, limb3]
    iterate 18
      refine Eq.trans (ite_eq_left ?_) ?_
      first
      | apply guardStore _ (by decide +kernel)
        repeat' apply Writable.memStore
        exact localSlot _ _ (by decide)
      | apply LoadOk.of_region (a := _) (h₁ := Nat.le_refl _) (h₂ := Nat.le_refl _)
        repeat' apply Readable.memStore
        first | exact srcBase | exact srcSlot _ (by decide) | exact (localSlot _ _ (by decide)).readable
    rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rintro ⟨i, _⟩ hi
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact congrArg Value.width cx | exact congrArg Value.width rdi
    · rintro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem Encode.enterLoop {fr : Activation} {a : Verify.Core.Registers} {x : Nat}
    (entry : Atom.All Extracted.programImage a fr.original (Fn100000.frameAt .l100000 fr))
    (depth : 208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 208)
    (orderAfter : fr.rsp.toNat ≤ fr.rsi.toNat) (len : fr.rcx = 32)
    (orderRead : Readable fr.original fr.rsi 32)
    (orderWords : WordsAt fr.original fr.rsi 64 (scalarWords Secp256k1.domain.n)) :
    ∃ b m, Verify.Core.Reaches .l100000 a fr.original (label 0) b m ∧
      Loop fr x 0 b m := by
  obtain ⟨b, run, rax, rdx, rsp, r12, widths, kept⟩ := orderLength entry depth orderAfter len orderRead orderWords
  have path : Verify.Core.Reaches .l100000 a fr.original .l1000cf b (entryMemory fr) :=
    .single (by change (program.runBlock _ _).next _ [] = _; rw [run]; rfl)
  let m := entryMemory fr
  simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨_, df, _, _, _, _, _, rdi, _, _, _, _, _, _, mx, ft, fc, retR, retM, retLow, stack, floor, align,
    gotR, gotM, _, _, _, _, apart, _⟩ := entry
  have di := (kept 7 (by decide)).trans rdi
  have cstep : ∃ c, Verify.Core.Reaches .l1000cf b m .l1000d8 c m ∧ c[0] = b[0] ∧
      ∀ i : Fin Reg.count, i.val ∈ [2, 4, 6, 7, 8, 9, 12, 22, 39, 50, 51] → c[i] = b[i] := by
    refine ⟨?_, .single ?run, ?zero, ?keep⟩
    case run =>
      change (program.runBlock _ _).next _ [] = _
      cfg_eval
      simp only [rdx]
      rfl
    case zero => rfl
    case keep =>
      rintro ⟨i, hi⟩ hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact rdx.symm
  obtain ⟨c, rc, c0, ck⟩ := cstep
  have cax := c0.trans rax
  have dstep : ∃ d, Verify.Core.Reaches .l1000d8 c m .l1000fb d m ∧ d[15] = ⟨64, 4⟩ ∧
      d[1].width = 64 ∧ ∀ i : Fin Reg.count, i.val ∈ [2, 4, 6, 7, 8, 9, 12, 22, 39, 50, 51] → d[i] = c[i] := by
    refine ⟨?_, .single ?run, ?cnt, ?w, ?rest⟩
    case run =>
      change (program.runBlock _ _).next _ [] = _
      cfg_eval
      simp only [cax]
      rfl
    case cnt => rfl
    case w => rfl
    case rest =>
      rintro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨d, rd, d15, d1, dk⟩ := dstep
  have same (i : Fin Reg.count) (hi : i.val ∈ [2, 4, 6, 7, 8, 9, 12, 22, 39, 50, 51])
      := (dk i hi).trans (ck i hi)
  have d2 := (same 2 (by decide)).trans rdx
  have d7 := (same 7 (by decide)).trans di
  have d12 := (same 12 (by decide)).trans r12
  refine ⟨?_, m, path.trans (rc.trans (rd.trans (.single ?run))), ?_⟩
  case run =>
    change (program.runBlock _ ⟨.l1000fb, d, m⟩).next _ [] = _
    cfg_eval
    rfl
  refine ⟨?atoms, d2, ?cursor, ?idx, ?zeroReg, d15, ?width, ?writes, fun i hi => by omega⟩
  case cursor => exact congrArg (fun (v : Value) => Value.mk 64 (v.get 64)) d2
  case idx => rfl
  case zeroReg => rfl
  case atoms =>
    change Atom.All _ _ _ (Fn100000.frameAt .l100110 fr)
    simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨(same 4 (by decide)).trans rsp, ?_,
      congrArg (fun (v : Value) => Value.mk 64 (v.get 64)) d7,
      congrArg (fun (v : Value) => Value.mk 64 (v.get 64)) d12, ?_, ?_, ?_, ?_⟩
    · exact (same 22 (by decide)).trans ((kept 22 (by decide)).trans df)
    · exact (same 39 (by decide)).trans ((kept 39 (by decide)).trans mx)
    · exact (same 50 (by decide)).trans ((kept 50 (by decide)).trans ft)
    · exact (same 51 (by decide)).trans ((kept 51 (by decide)).trans fc)
    · have wf := entryMemory_writes depth low []
      have base : fr.low.toNat = fr.rsp.toNat - 208 := by
        rw [low, BitVec.toNat_sub_of_le (by exact depth)]
        rfl
      have outside (p : BitVec 64) (bound : p.toNat + 8 ≤ 2^64)
          (disj : p.toNat + 8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ p.toNat) :
          Outside [fr.region] p 8 := by
        refine ⟨bound, ?_⟩
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        change p.toNat + 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ p.toNat
        omega
      have ret := (wf.memLoad_eq (k := 64) (outside fr.rsp (by have := retR.low; omega) (Or.inr (by omega)))).trans retM
      have got := (wf.memLoad_eq (k := 64) (outside 0x203dd0 (by decide) (by
        change 0x203dd0 + 8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x203dd0
        omega))).trans gotM
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, retR.of_frame wf, ret, retLow, stack.of_frame wf, floor, align,
        gotR.of_frame wf, got, by omega, trivial⟩ <;> unfold m entryMemory <;> segment_words []
  case width =>
    rintro ⟨i, hi⟩ member
    have w := widths ⟨i, hi⟩ member
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (congrArg Value.width (same 7 (by decide))).trans w
    · exact (congrArg Value.width (same 6 (by decide))).trans w
    · exact (congrArg Value.width (same 2 (by decide))).trans w
    · exact d1
    · exact (congrArg Value.width (same 8 (by decide))).trans w
    · exact (congrArg Value.width (same 9 (by decide))).trans w
  case writes => exact entryMemory_writes depth low _

end K256.Proofs.Signing.Nonce.Initialize
