import K256.Proofs.Sec1.Serialize.Control
import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Sec1.Serialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

theorem copyAndReturn {args : Vector Value 53} {m : Ram} {sp dst : BitVec 64}
    (rsp : Value.get 64 args[4] = sp) (rbx : Value.get 64 args[3] = dst)
    (df : Value.get 1 args[22] = 0)
    (stack : Readable m sp 320) (room : 8 ≤ sp.toNat)
    (push : Writable Extracted.programImage m (sp - 8) 8)
    (dest : Writable Extracted.programImage m dst 65)
    (apart : dst.toNat + 65 ≤ sp.toNat - 8 ∨ sp.toNat + 320 ≤ dst.toNat)
    (load : LoadOk m 0x203dd0 8) (target : memLoad m 0x203dd0 64 = 0x12a820)
    (low : (memLoad m (sp + 312) 64).toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1218bb, args, m⟩, []⟩ out ∧
      out.store = memCopy (memStore m (sp - 8) (0x1218ce : BitVec 64)) dst (sp + 80) 65 ∧
      RamWriteFrame m out.store [⟨dst.toNat, 65⟩, ⟨(sp - 8).toNat, 8⟩] ∧
      (∀ bytes, (⟨(sp + 80).toNat, 65⟩ : MemoryRegion).HasBytes m bytes →
        (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes out.store bytes) ∧
      out.tag = some ⟨64, memLoad m (sp + 312) 64⟩ ∧
      out.values[0] = ⟨64, dst⟩ ∧ out.values[4] = ⟨64, sp + 320⟩ ∧
      out.values[3] = ⟨64, memLoad m (sp + 280) 64⟩ ∧
      out.values[14] = ⟨64, memLoad m (sp + 288) 64⟩ ∧
      out.values[15] = ⟨64, memLoad m (sp + 296) 64⟩ ∧
      out.values[5] = ⟨64, memLoad m (sp + 304) 64⟩ ∧
      ∀ i : Fin 53, i.val ∈ [12,13,22,39,50,51] → out.values[i] = args[i] := by
  let code := Extracted.programImage
  let pushed := memStore m (sp - 8) (0x1218ce : BitVec 64)
  let child := (((args.set 2 ⟨64, 65⟩).set 4 ⟨64, sp - 8⟩).set 6 ⟨64, sp + 80⟩).set 7 ⟨64, dst⟩
  have hsp := stack.low
  have hd := dest.readable.low
  have start : (sp - 8).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact room)]
    rfl
  have offset (i : Nat) (hi : i ≤ 320) : (sp + BitVec.ofNat 64 i).toNat = sp.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have srcAt : (sp + 80).toNat = sp.toNat + 80 := offset 80 (by decide)
  have guard : StoreOk code m (sp - 8) 8 0x1218c8 6 :=
    ParseSignature.storeOk_of_codeRange (off := 13) push
      (fun x hx => Common.fnCode_subset_programImage x (code_l1218bb x hx)) (by decide)
  have setup := copySetup rsp rbx guard load target
  have ret : memLoad pushed (sp - 8) 64 = 0x1218ce :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have rd : Readable pushed (sp + 80) 65 :=
    (stack.of_offsets rfl (addr_self sp) (by decide)).memStore _ _
  have sep : (sp + 80).toNat + 65 ≤ dst.toNat ∨ dst.toNat + 65 ≤ (sp + 80).toNat := by
    rw [srcAt]
    omega
  have retApart : RangeApart dst 65 (sp - 8) 8 := by
    apply RangeApart.of_toNat <;> omega
  have hdf : child[22].get 1 = 0 := by simpa [child] using df
  obtain ⟨copy, ran, copied, rip, _, newSP, kept⟩ :=
    Wrapper.Copy.memcpy (args := child) (count := 65) (rsp := sp - 8)
      (by simp [child]) (by simp [child]) (by simp [child]) (by simp [child])
      hdf rd (dest.memStore _ _) sep retApart (push.readable.memStore _ _) (by rw [ret]; decide)
  rw [ret] at rip
  let regions : List MemoryRegion := [⟨dst.toNat, 65⟩, ⟨(sp - 8).toNat, 8⟩]
  have frame : RamWriteFrame m copy.store regions := by
    rw [copied]
    have pushedFrame : RamWriteFrame m pushed regions := (RamWriteFrame.refl _ _).memStore _
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _,
        by change (sp - 8).toNat + 8 ≤ 2^64; omega⟩
    exact pushedFrame.memStore _ ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _,
      by change dst.toNat + 65 ≤ 2^64; omega⟩
  have saved (i : Nat) (hi : i + 8 ≤ 320) :
      memLoad copy.store (sp + BitVec.ofNat 64 i) 64 = memLoad m (sp + BitVec.ofNat 64 i) 64 := by
    apply frame.memLoad_eq
    refine ⟨by rw [offset i (by omega)]; change sp.toNat + i + 8 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [offset i (by omega), start, Nat.reduceDiv] <;> omega
  have slots (i : Nat) (hi : i ∈ [280,288,296,304,312]) : LoadOk copy.store (sp + BitVec.ofNat 64 i) 8 := by
    have bound : i + 8 ≤ 320 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    exact LoadOk.of_region (stack.of_frame frame) (by rw [offset i (by omega)]; omega)
      (by rw [offset i (by omega)]; omega)
  have sp' : Value.get 64 copy.values[4] = sp := by rw [newSP, BitVec.sub_add_cancel]; rfl
  have ret' : (memLoad copy.store (sp + 312) 64).toNat < 2^32 := (saved 312 (by decide)) ▸ low
  obtain ⟨out, finish, memory, tag, rax, outSP, bx, r14, r15, bp, rest⟩ :=
    returnBlock (code := code) sp' slots ret'
  have run : program.Exec (dialect code) ⟨⟨.l1218bb, args, m⟩, []⟩ out := by
    apply ParseSignature.exec_call setup ran (by rw [rip]; rfl)
    exact .done (congrArg (Transfer.next _ []) finish)
  refine ⟨out, run, memory.trans copied, memory ▸ frame, ?_, tag.trans ?_, rax.trans ?_, outSP,
    bx.trans ?_, r14.trans ?_, r15.trans ?_, bp.trans ?_, ?_⟩
  · intro bytes source
    rw [memory, copied]
    apply Wrapper.Copy.memCopy_hasBytes (by decide)
    refine ⟨source.1, fun i => ?_⟩
    rw [← source.2 i]
    change pushed[BitVec.ofNat 64 ((sp + 80).toNat + i.val)]? = _
    apply memStore_getElem?_of_ne
    intro j hj h
    have len : bytes.size = 65 := source.1
    have ib := i.isLt
    have left := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, start, BitVec.toNat_ofNat, srcAt] at left
    change j < 8 at hj
    omega
  · exact congrArg (fun v => some (⟨64, v⟩ : Value)) (saved 312 (by decide))
  · have h := kept 3 (by decide)
    change copy.values[3] = child[3] at h
    rw [h]
    simpa [child] using congrArg (fun v => (⟨64, v⟩ : Value)) rbx
  · exact congrArg (fun v => (⟨64, v⟩ : Value)) (saved 280 (by decide))
  · exact congrArg (fun v => (⟨64, v⟩ : Value)) (saved 288 (by decide))
  · exact congrArg (fun v => (⟨64, v⟩ : Value)) (saved 296 (by decide))
  · exact congrArg (fun v => (⟨64, v⟩ : Value)) (saved 304 (by decide))
  · intro i hi
    have k := kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
    refine (rest i hi).trans (k.trans ?_)
    change child[i.val] = args[i.val]
    obtain ⟨i, bound⟩ := i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [child, Vector.getElem_set] <;> rfl

end K256.Proofs.Sec1.Serialize
