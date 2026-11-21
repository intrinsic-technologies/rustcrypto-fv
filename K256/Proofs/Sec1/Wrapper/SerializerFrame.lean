import K256.Proofs.Sec1.Wrapper.Contracts
import K256.Proofs.Sec1.Wrapper.Calls
import K256.Proofs.Sec1.Parser.Memory
import K256.Proofs.Sec1.Serialize.Contract

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC

private theorem offsetNat {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    {n : Nat} (depth : n ≤ 1928) :
    (s.regValue .rsp - BitVec.ofNat 64 n).toNat = (s.regValue .rsp).toNat - n := by
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have hn : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn]; omega), hn]

theorem serializerEntry {s : RamState} {bytes : ByteArray} {args : Vector Value 53} {mem : Ram}
    {point : Curve.Point} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (frame : CallerFrame s [stack s] args mem)
    (hPoint : Parser.PublicKeyAt mem (s.regValue .rsp - 104) point) :
    let sp := s.regValue .rsp
    let entry := sp - 256
    let src := sp - 104
    let dst := sp - 233
    let child := memStore mem entry (0x101e0c : BitVec 64)
    Parser.PublicKeyAt child src point ∧
      Readable child src 88 ∧ Writable Extracted.programImage child dst 65 ∧
      Writable Extracted.programImage child (entry - 448) 456 ∧
      Readable child entry 8 ∧ memLoad child entry 64 = 0x101e0c ∧
      entry.toNat % 16 = 8 ∧ 448 ≤ entry.toNat ∧
      entry.toNat + 8 ≤ dst.toNat ∧ dst.toNat + 65 ≤ src.toNat ∧
      LoadOk child 0x203dd0 8 ∧ memLoad child 0x203dd0 64 = 0x12a820 := by
  intro sp entry src dst child
  obtain ⟨x,y,pointEq,atPoint⟩ := hPoint
  have room : 1928 ≤ sp.toNat := call.stackAvailable.2.2.1
  have align : sp.toNat % 16 = 8 := call.stackAvailable.2.2.2
  have en : entry.toNat = sp.toNat - 256 := offsetNat call (by decide : 256 ≤ 1928)
  have dn : dst.toNat = sp.toNat - 233 := offsetNat call (by decide : 233 ≤ 1928)
  have sn : src.toNat = sp.toNat - 104 := offsetNat call (by decide : 104 ≤ 1928)
  have access {n len : Nat} (depth : n ≤ 1928) (fits : len ≤ n + 8) (pos : 0 < len) :=
    ((stackWritable call depth fits pos).of_frame frame.writes).memStore entry (0x101e0c : BitVec 64)
  have push := frame.writes.memStore (0x101e0c : BitVec 64)
    (Parser.stackRange (off := 256) call (by decide) (by decide))
  have got := memcpy_target_load (Parser.inputs_of_stackFrame call push).2
  have separated : RangeApart entry 8 src 88 := RangeApart.of_offsets (addr_sub sp 256) (addr_sub sp 104) (by decide)
  refine ⟨⟨x,y,pointEq,atPoint.of_copy ?_⟩, (access (by decide : 104 ≤ 1928) (by decide) (by decide)).readable,
    access (by decide : 233 ≤ 1928) (by decide) (by decide), ?_,
    (access (by decide : 256 ≤ 1928) (by decide) (by decide)).readable,
    memLoad_memStore_same mem _ _ (by decide) (by decide), by omega, by omega, by omega, by omega, got⟩
  · intro off width fits
    exact memLoad_memStore_of_rangeApart mem _ _ _ _ (RangeApart.right_sub separated fits)
  · have low : entry - 448 = sp - 704 := by dsimp only [entry]; rw [BitVec.sub_sub]; rfl
    rw [low]
    exact access (by decide : 704 ≤ 1928) (by decide) (by decide)

theorem serializerFrame {s : RamState} {bytes : ByteArray} {args : Vector Value 53} {mem : Ram}
    {out : Output Value Ram 53} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (frame : CallerFrame s [stack s] args mem)
    (rsp : out.values[4] = ⟨64, s.regValue .rsp - 256 + 8⟩)
    (kept : ∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15,22] → out.values[i] = args[i])
    (written : let sp := s.regValue .rsp
      RamWriteFrame (memStore mem (sp - 256) (0x101e0c : BitVec 64)) out.store
        [⟨(sp - 256 - 448).toNat, 448⟩, ⟨(sp - 233).toNat, 65⟩]) :
    CallerFrame s [stack s] out.values out.store ∧ out.values[3] = args[3] := by
  let sp := s.regValue .rsp
  let regions : List MemoryRegion := [⟨(sp - 704).toNat, 448⟩, ⟨(sp - 233).toNat, 65⟩]
  let m := memStore mem (sp - 256) (0x101e0c : BitVec 64)
  have writes : RamWriteFrame m out.store regions := by
    simpa only [BitVec.sub_sub, show (256 : BitVec 64) + 448 = 704 by rfl] using written
  have n₁ : (sp - 704).toNat = sp.toNat - 704 := offsetNat call (by decide : 704 ≤ 1928)
  have n₂ : (sp - 233).toNat = sp.toNat - 233 := offsetNat call (by decide : 233 ≤ 1928)
  have room : 1928 ≤ sp.toNat := call.stackAvailable.2.2.1
  have low : sp.toNat + 8 < 2^32 := by
    have hb := call.stackAvailable.1
    change sp.toNat - 1928 + (sp.toNat + 8 - (sp.toNat - 1928)) < 2^32 at hb
    omega
  have inside : RegionsWithin regions [stack s] := by
    intro r hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rcases List.mem_cons.mp hr with rfl | ht
    · change sp.toNat - 1928 ≤ (sp - 704).toNat ∧ (sp - 704).toNat + 448 ≤
        sp.toNat - 1928 + (sp.toNat + 8 - (sp.toNat - 1928))
      omega
    · obtain rfl := List.mem_singleton.mp ht
      change sp.toNat - 1928 ≤ (sp - 233).toNat ∧ (sp - 233).toNat + 65 ≤
        sp.toNat - 1928 + (sp.toNat + 8 - (sp.toNat - 1928))
      omega
  have slot {a : BitVec 64} (hi : sp.toNat - 16 ≤ a.toNat) (ha : a.toNat ≤ sp.toNat)
      (apart : RangeApart (sp - 256) 8 a 8) : memLoad out.store a 64 = memLoad mem a 64 := by
    refine (writes.memLoad_eq ⟨by omega, fun r hr => Or.inr ?_⟩).trans
      (memLoad_memStore_of_rangeApart mem _ _ _ _ apart)
    rcases List.mem_cons.mp hr with rfl | ht
    · change (sp - 704).toNat + 448 ≤ a.toNat
      omega
    · obtain rfl := List.mem_singleton.mp ht
      change (sp - 233).toNat + 65 ≤ a.toNat
      omega
  have slotAt (off : Nat) (small : off ≤ 16) :
      memLoad out.store (sp - BitVec.ofNat 64 off) 64 = memLoad mem (sp - BitVec.ofNat 64 off) 64 := by
    have atNat : (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := offsetNat call (by omega)
    apply slot (by omega) (by omega)
    have mid : RangeApart (sp - 256) 8 (sp - 16) 24 :=
      RangeApart.of_offsets (addr_sub sp 256) (addr_sub sp 16) (by decide)
    have eq : sp - 16 + BitVec.ofNat 64 (16 - off) = sp - BitVec.ofNat 64 off := by
      have : BitVec.ofNat 64 (16 - off) + BitVec.ofNat 64 off = 16 := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel small]; rfl
      bv_omega
    rw [← eq]
    exact RangeApart.right_sub mid (by omega)
  have hp := frame.writes.memStore (0x101e0c : BitVec 64) (Parser.stackRange (off := 256) call (by decide) (by decide))
  refine ⟨⟨rsp.trans (congrArg (fun b => (⟨64,b⟩ : Value)) (by change sp - 256 + 8 = sp - 248; bv_omega)),
    (kept 14 (by decide)).trans frame.dst, ?_, (slotAt 16 (by decide)).trans frame.rbx,
    (slotAt 8 (by decide)).trans frame.r14, ?_, hp.trans writes inside⟩, kept 3 (by decide)⟩
  · intro i hi
    exact (kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans (frame.kept i hi)
  · have ret : memLoad out.store sp 64 = memLoad mem sp 64 := by
      have e := slotAt 0 (by decide)
      change memLoad out.store (sp - 0) 64 = memLoad mem (sp - 0) 64 at e
      rwa [show sp - 0 = sp by bv_omega] at e
    exact ret.trans frame.ret

theorem serializerCall {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (exec : Serialize.SerializerExecution) :
    SerializerCall s := by
  let sp := s.regValue .rsp
  intro args mem point frame status atPoint
  let child := (((args.set 2 ⟨64, 0⟩).set 4 ⟨64, sp - 256⟩).set 6 ⟨64, sp - 104⟩).set 7 ⟨64, sp - 233⟩
  have same (i : Fin 53) (hi : i.val ∈ [3,5,12,13,14,15,22]) : child[i] = args[i] := by
    change child[i.val] = args[i.val]
    simp only [child, Vector.getElem_set]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h <;> simp [h]
  have width (i : Fin 53) (hi : i.val ∈ [3,5,12,13,14,15]) : child[i].width = 64 := by
    rw [same i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    by_cases h3 : i = 3
    · subst i
      exact congrArg Value.width status
    by_cases h14 : i = 14
    · subst i
      exact congrArg Value.width frame.dst
    have hk : i.val ∈ [5,12,13,15,22] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rw [frame.kept i hk]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h <;> obtain ⟨j, hj⟩ := i <;> subst_vars <;> rfl
  have df := (same 22 (by decide)).trans ((frame.kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset))
  obtain ⟨hp, hr, hd, hs, _, hret, align, room, lower, upper, gotOk, gotVal⟩ := serializerEntry call frame atPoint
  obtain ⟨out, run, tag, rsp, kept, writes, prefixByte, encoded⟩ :=
    exec (args := child) (by simp only [child, Vector.getElem_set]; rfl)
      (by simp only [child, Vector.getElem_set]; rfl) (by simp only [child, Vector.getElem_set]; rfl)
      (by simp only [child, Vector.getElem_set]; rfl) df width hp hr hd hs hret (by decide)
      align room lower upper gotOk gotVal
  obtain ⟨restored, rbx⟩ := serializerFrame call frame rsp (fun i hi =>
    (kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans (same i hi)) writes
  exact ⟨out, run, tag, restored, rbx.trans status, prefixByte, encoded⟩

end K256.Proofs.Sec1.Wrapper
