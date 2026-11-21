import K256.Proofs.Generate.Wrapper.Memory
import K256.Proofs.Generate.Serialize.Transfer
import K256.Proofs.Sec1.Wrapper.Calls
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Generate.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters K256.Proofs.Generate.LIR

variable {s : RamState} {random : ByteArray} {args : Vector Value Reg.count} {mem : Ram}

private def tagArgs (args : Vector Value Reg.count) : Vector Value Reg.count :=
  (((args.set 0 ⟨64, mergeGPR 8 1 (args[0].get 64)⟩).set 1 ⟨64, 4⟩).set 2
    ⟨64, mergeGPR 8 3 (args[2].get 64)⟩).set 19 (.ofBool false)

private theorem tagDispatch {code : CodeMap} {src : BitVec 64}
    (rsp : args[4].get 64 = src) (read : LoadOk mem src 1) (tag : memLoad mem src 8 = 4) :
    program.runBlock (dialect code) ⟨.l102575, args, mem⟩ =
      .jump ⟨.l1025ba, tagArgs args, mem⟩ := by
  cfg_eval [rsp, read, tag]
  have carry : (cmpSpec (4 : BitVec 64) 6).CF = true := by decide +kernel
  have shift : ((61 : BitVec 8) >>> shiftCount 8 4) = 3 := by decide +kernel
  have test : (testFlags ((1 : BitVec 8) &&& 3)).ZF.getD false = false := by decide +kernel
  simp only [carry, ↓reduceIte, setWidth_mergeGPR8]
  simp only [shift, test, mergeGPR_mergeGPR 8 (Or.inl rfl), Bool.not_false, ↓reduceIte]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [tagArgs, Vector.getElem_set] <;> rfl

private def copyArgs (args : Vector Value Reg.count) (src dst : BitVec 64) :
    Vector Value Reg.count :=
  ((((args.set 2 ⟨64, 65⟩).set 3 ⟨64, dst + 32⟩).set 4 ⟨64, src - 8⟩).set
    6 ⟨64, src⟩).set 7 ⟨64, dst + 32⟩

private def copyReturn : StackFrame Value Label signature Reg.count :=
  { target := .l1025d2, kept := #v[], arity := rfl, guard := some ⟨64, 0x1025d2⟩ }

private theorem copyCall {code : CodeMap} {src dst : BitVec 64}
    (rsp : args[4].get 64 = src) (rbx : args[3].get 64 = dst) (tag : args[1].get 64 = 4)
    (push : StoreOk code mem (src - 8) 8 0x1025cc 6)
    (table : LoadOk mem 0x2022d8 8) (len : memLoad mem 0x2022d8 64 = 65)
    (got : LoadOk mem 0x203dd0 8) (target : memLoad mem 0x203dd0 64 = 0x12a820) :
    program.runBlock (dialect code) ⟨.l1025ba, args, mem⟩ =
      .call ⟨.l12a820, copyArgs args src dst, memStore mem (src - 8) (0x1025d2 : BitVec 64)⟩
        copyReturn := by
  have address : ((4 : BitVec 64) <<< 3) + 0x2022b8 = 0x2022d8 := rfl
  cfg_eval
  simp only [rsp, rbx, tag, address, table, len, got, target, push, and_self, ↓reduceIte]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [copyArgs, Vector.getElem_set] <;> rfl

private theorem bytes_memStore_of_apart {p q : BitVec 64} {n w : Nat} {bytes : ByteArray}
    (v : BitVec w) (apart : RangeApart p (w / 8) q n) (hb : atBytes q n mem bytes) :
    atBytes q n (memStore mem p v) bytes := by
  refine ⟨hb.1, fun i => ?_⟩
  have h := hb.2 i
  have size : bytes.size = n := hb.1
  have hi : i.val < n := size ▸ i.isLt
  change (memStore mem p v)[BitVec.ofNat 64 (q.toNat + i.val)]? = _
  change mem[BitVec.ofNat 64 (q.toNat + i.val)]? = _ at h
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h ⊢
  rw [memStore_getElem?_of_ne _ _ _ _ (fun j hj => apart j hj i.val hi)]
  exact h

theorem copy {d : Nat} {pt : Curve.Point} (call : ValidCall signingKeyGenerateFromRng s [random])
    (f : CallerFrame s args mem) (dst : args[3] = ⟨64, s.regValue .rdi⟩)
    (tag : memLoad mem (s.regValue .rsp - 280) 8 = 4)
    (scalar : atBytes (s.regValue .rdi) 32 mem (Encoding.natToOctets 32 d))
    (encoded : atBytes (s.regValue .rsp - 280) 65 mem (Points.encodePoint Secp256k1.domain false pt)) :
    ∃ a m, Segment .l102575 args mem .l1025d2 a m ∧ CallerFrame s a m ∧
      atBytes (s.regValue .rdi) 32 m (Encoding.natToOctets 32 d) ∧
      atBytes (s.regValue .rdi + 32) 65 m (Points.encodePoint Secp256k1.domain false pt) := by
  let sp := s.regValue .rsp
  let src := sp - 280
  let dest := s.regValue .rdi
  let dstPoint := dest + 32
  let slot := src - 8
  let next := tagArgs args
  let child := copyArgs next src dest
  let pushed := memStore mem slot (0x1025d2 : BitVec 64)
  have slotAddr : slot = sp - 288 := by dsimp only [slot, src]; bv_omega
  have room : 10584 ≤ sp.toNat := call.stackAvailable.2.2.1
  have srcNat : src.toNat = sp.toNat - 280 := stackOffset (off := 280) call (by decide)
  have slotNat : slot.toNat = sp.toNat - 288 := by
    rw [slotAddr]
    exact stackOffset (off := 288) call (by decide)
  have separated := output_stack_apart call
  change dest.toNat + 97 ≤ sp.toNat - 10584 ∨ sp.toNat + 8 ≤ dest.toNat at separated
  have srcWrite : Writable Extracted.programImage mem src 65 :=
    (stackWritable (off := 280) (len := 65) call (by decide) (by decide) (by decide)).of_frame f.writes
  have slotWrite : Writable Extracted.programImage mem slot 8 := by
    rw [slotAddr]
    exact (stackWritable (off := 288) (len := 8) call (by decide) (by decide) (by decide)).of_frame f.writes
  have destWrite : Writable Extracted.programImage mem dest 97 :=
    (outputWritable call).of_frame f.writes
  have destLow : dest.toNat + 97 ≤ 2^32 := destWrite.readable.low
  have dstNat : dstPoint.toNat = dest.toNat + 32 := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by change dest.toNat + 32 < 2^64; omega)
  have pointWrite : Writable Extracted.programImage mem dstPoint 65 :=
    destWrite.sub (by omega) (by omega)
  have slotLow : slot.toNat + 8 ≤ 2^32 := slotWrite.readable.low
  have srcLow : src.toNat + 65 ≤ 2^32 := srcWrite.readable.low
  have rsp : args[4].get 64 = src := by rw [f.rsp]; rfl
  have dispatch := tagDispatch (code := Extracted.programImage) rsp
    (LoadOk.of_region srcWrite.readable (Nat.le_refl _) (by omega)) tag
  have push : StoreOk Extracted.programImage mem slot 8 0x1025cc 6 :=
    ParseSignature.storeOk_of_codeRange (off := 18) slotWrite
      (fun x hx => Common.fnCode_subset_programImage x (code_l1025ba x hx)) (by decide)
  have loaded := image_of_frame call f.writes
  obtain ⟨table, length⟩ := Sec1.Wrapper.memcpy_length_load loaded 4
  obtain ⟨got, target⟩ := Sec1.Wrapper.memcpy_target_load loaded
  have called := copyCall
    (show next[4].get 64 = src by simp only [next, tagArgs, Vector.getElem_set]; exact rsp)
    (show next[3].get 64 = dest by simp only [next, tagArgs, Vector.getElem_set]; rw [dst]; rfl)
    (show next[1].get 64 = 4 by simp only [next, tagArgs, Vector.getElem_set]; rfl) push table length got target
  have slotValue : memLoad pushed slot 64 = 0x1025d2 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have saved (i : Fin 53) (hi : i.val ∈ [5, 12, 13, 15, 22]) : child[i] = args[i] := by
    change child[i.val] = args[i.val]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h <;>
      simp only [child, next, copyArgs, tagArgs, Vector.getElem_set, h] <;> rfl
  have df : child[22].get 1 = 0 :=
    congrArg (Value.get 1) ((saved 22 (by decide)).trans
      ((f.kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset)))
  have apartStack (off : Nat) (depth : off ≤ 10584) :
      RangeApart dstPoint 65 (sp - BitVec.ofNat 64 off) 8 := by
    have nat : (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := stackOffset call depth
    have low := (stackRange (off := off) (len := 8) call depth (by omega)).2.2
    apply RangeApart.of_toNat (by omega) low
    change dstPoint.toNat + 65 ≤ (sp - BitVec.ofNat 64 off).toNat ∨
      (sp - BitVec.ofNat 64 off).toNat + 8 ≤ dstPoint.toNat
    omega
  obtain ⟨out, run, store, ret, _, returnedSp, kept⟩ := Serialize.memcpy
    (args := child) (mem := pushed) (dst := dstPoint) (src := src) (count := 65) (rsp := slot)
    (by simp only [child, copyArgs, Vector.getElem_set]; rfl)
    (by simp only [child, copyArgs, Vector.getElem_set]; rfl)
    (by simp only [child, copyArgs, Vector.getElem_set]; rfl)
    (by simp only [child, copyArgs, Vector.getElem_set]; rfl) df (srcWrite.readable.memStore _ _) (pointWrite.memStore _ _)
    (by change src.toNat + 65 ≤ dstPoint.toNat ∨ dstPoint.toNat + 65 ≤ src.toNat; omega)
    (slotAddr ▸ apartStack 288 (by decide)) (slotWrite.readable.memStore _ _) (by rw [slotValue]; decide)
  change out.store = memCopy pushed dstPoint src 65 at store
  rw [slotValue] at ret
  have resume := ParseSignature.exec_reaches_resume run copyReturn [] (by rw [ret]; rfl)
  have segment : Segment .l102575 args mem .l1025d2 out.values out.store := by
    refine .step (congrArg (Transfer.next _ []) dispatch) ?_
    exact .step (congrArg (Transfer.next _ []) called) resume
  have unchanged (off : Nat) (near : off ≤ 16) :
      memLoad out.store (sp - BitVec.ofNat 64 off) 64 = memLoad mem (sp - BitVec.ofNat 64 off) 64 := by
    rw [store]
    unfold memCopy pushed
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apartStack off (by omega)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (by
        have nat : (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off :=
          stackOffset call (by omega)
        have low := (stackRange (off := off) (len := 8) call (by omega) (by omega)).2.2
        apply RangeApart.of_toNat (by omega) low
        left
        change slot.toNat + 8 ≤ (sp - BitVec.ofNat 64 off).toNat
        omega)]
  have slotFrame : RamWriteFrame s.external pushed (regions s).toList := by
    apply f.writes.memStore
    exact ⟨_, by simp [regions], slotAddr ▸ stackRange (off := 288) call (by decide) (by decide)⟩
  refine ⟨out.values, out.store, segment, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have h : slot + 8 = src := by dsimp only [slot]; bv_omega
    exact returnedSp.trans (by rw [h])
  · intro i hi
    exact (kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      ((saved i hi).trans (f.kept i hi))
  · exact (unchanged 16 (by decide)).trans f.rbx
  · exact (unchanged 8 (by decide)).trans f.r14
  · have h := unchanged 0 (by decide)
    have addr : sp - BitVec.ofNat 64 0 = sp := BitVec.sub_zero _
    rw [addr] at h
    exact h.trans f.ret
  · rw [store]
    apply Sec1.Wrapper.Copy.memCopy_frame slotFrame
    exact ⟨outputRegion signingKeyGenerateFromRng s, by simp [regions],
      (by change dest.toNat ≤ dstPoint.toNat; omega),
      (by change dstPoint.toNat + 65 ≤ dest.toNat + 97; omega), by omega⟩
  · change atBytes dest 32 out.store _
    rw [store]
    unfold memCopy
    apply bytes_memStore_of_apart
    · apply RangeApart.of_toNat (by omega) (by omega) (Or.inr (by omega))
    · apply bytes_memStore_of_apart
      · apply RangeApart.of_toNat (by omega) (by omega)
        omega
      · exact scalar
  · rw [store]
    apply Sec1.Wrapper.Copy.memCopy_hasBytes (by decide)
    apply bytes_memStore_of_apart
    · exact RangeApart.of_toNat (by omega) (by omega) (Or.inl (by omega))
    · exact encoded

end K256.Proofs.Generate.Wrapper
