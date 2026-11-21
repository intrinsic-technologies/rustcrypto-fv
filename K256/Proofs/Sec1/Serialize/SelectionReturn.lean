import K256.Proofs.Sec1.Serialize.Layout
import K256.Proofs.Sec1.Serialize.SelectSetup
import K256.Proofs.Sec1.Serialize.Finish

namespace K256.Proofs.Sec1.Serialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

theorem selectAndReturn {args : Vector Value Reg.count} {mem : Ram} {sp dst : BitVec 64}
    {bytes : ByteArray} (hsp : args[4] = ⟨64,sp⟩) (hdst : args[3] = ⟨64,dst⟩)
    (sel : args[0].get 8 = 0) (df : args[22].get 1 = 0)
    (window : Writable Extracted.programImage mem (sp - 9) 329)
    (room : 9 ≤ sp.toNat) (apart : sp.toNat + 320 ≤ dst.toNat)
    (dest : Writable Extracted.programImage mem dst 65)
    (got : LoadOk mem 0x203dd0 8) (ptr : memLoad mem 0x203dd0 64 = 0x12a820)
    (low : (memLoad mem (sp + 312) 64).toNat < 2^32)
    (payload : (⟨(sp + 215).toNat, 65⟩ : MemoryRegion).HasBytes mem bytes) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121831,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64, memLoad mem (sp + 312) 64⟩ ∧ out.values[4] = ⟨64, sp + 320⟩ ∧
      out.values[3] = ⟨64, memLoad mem (sp + 280) 64⟩ ∧
      out.values[14] = ⟨64, memLoad mem (sp + 288) 64⟩ ∧
      out.values[15] = ⟨64, memLoad mem (sp + 296) 64⟩ ∧
      out.values[5] = ⟨64, memLoad mem (sp + 304) 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [12,13,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame mem out.store [⟨(sp - 9).toNat, 289⟩, ⟨dst.toNat, 65⟩] ∧
      (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes out.store bytes := by
  have base : (sp - 9).toNat = sp.toNat - 9 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact room)]
    rfl
  have lowMem := window.readable.low
  have add (n : Nat) (hn : n ≤ 320) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have a7 : (sp + 7).toNat = sp.toNat + 7 := add 7 (by decide)
  have a80 : (sp + 80).toNat = sp.toNat + 80 := add 80 (by decide)
  have slot : (sp - 8).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ sp.toNat; omega)]
    rfl
  have sub := window.of_offsets (a := sp + 7) rfl (addr_sub sp 9) (n := 273) (by decide)
  obtain ⟨b, t, reach, _, kept, loopFrame, bytesAt⟩ := selectionFromSetup
    (calls := []) Common.fnCode_subset_programImage sub hsp sel payload
  have regs (i : Fin Reg.count) (hi : i.val ∈ [3,4,12,13,22,39,50,51]) : b[i] = args[i] :=
    kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  have slots (r : MemoryRegion) (hr : r ∈ selectionWrites sp) :
      sp.toNat ≤ r.start ∧ r.start + r.size ≤ sp.toNat + 145 := by
    simp only [selectionWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [a7,a80] <;> omega
  have safe (i : Nat) (lo : 280 ≤ i) (hi : i ≤ 312) :
      memLoad t (sp + BitVec.ofNat 64 i) 64 = memLoad mem (sp + BitVec.ofNat 64 i) 64 := by
    apply loopFrame.memLoad_eq
    refine ⟨by rw [add i (by omega)]; change sp.toNat + i + 8 ≤ 2^64; omega,
      fun r hr => Or.inr ?_⟩
    rw [add i (by omega)]
    have := slots r hr
    omega
  have gotApart := writable_copy_slot_apart window (by decide)
  have gotValue : memLoad t 0x203dd0 64 = 0x12a820 := by
    rw [← ptr]
    apply loopFrame.memLoad_eq
    refine ⟨by decide, fun r hr => ?_⟩
    have := slots r hr
    change 0x203dd0 + 8 ≤ r.start ∨ r.start + r.size ≤ 0x203dd0
    omega
  have gotRead : LoadOk t 0x203dd0 8 :=
    ⟨got.1, fun i hi => loopFrame.present _ (got.2 i hi)⟩
  have hstack := window.of_frame loopFrame
  have stackReadable : Readable t sp 320 :=
    hstack.readable.of_offsets (addr_self sp) (addr_sub sp 9) (by decide)
  obtain ⟨out, run, _, written, copied, tag, _, rsp, bx, r14, r15, bp, same⟩ :=
    copyAndReturn (args := b) (sp := sp) (dst := dst) (congrArg (Value.get 64) ((regs 4 (by decide)).trans hsp))
      (congrArg (Value.get 64) ((regs 3 (by decide)).trans hdst)) ((congrArg (Value.get 1) (regs 22 (by decide))).trans df)
      stackReadable (by omega)
      (hstack.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)) (dest.of_frame loopFrame)
      (Or.inr apart) gotRead gotValue (by
        have e : memLoad t (sp + 312) 64 = memLoad mem (sp + 312) 64 := safe 312 (by decide) (by decide)
        rwa [e])
  refine ⟨out, Program.Exec.of_sem (reach.exec run.sem), tag.trans ?_, rsp,
    bx.trans ?_, r14.trans ?_, r15.trans ?_, bp.trans ?_, ?_, ?_, copied bytes bytesAt⟩
  · exact congrArg (fun v => some (⟨64,v⟩ : Value)) (safe 312 (by decide) (by decide))
  · exact congrArg (fun v => (⟨64,v⟩ : Value)) (safe 280 (by decide) (by decide))
  · exact congrArg (fun v => (⟨64,v⟩ : Value)) (safe 288 (by decide) (by decide))
  · exact congrArg (fun v => (⟨64,v⟩ : Value)) (safe 296 (by decide) (by decide))
  · exact congrArg (fun v => (⟨64,v⟩ : Value)) (safe 304 (by decide) (by decide))
  · intro i hi
    exact (same i hi).trans (regs i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  · refine ((RamWriteFrame.refl mem _).trans loopFrame ?_).trans written ?_
    · intro r hr
      refine ⟨_, List.mem_cons_self .., ?_⟩
      have := slots r hr
      change (sp - 9).toNat ≤ r.start ∧ r.start + r.size ≤ (sp - 9).toNat + 289
      omega
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | ht
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
      · obtain rfl := List.mem_singleton.mp ht
        refine ⟨_, List.mem_cons_self .., ?_⟩
        change (sp - 9).toNat ≤ (sp - 8).toNat ∧ (sp - 8).toNat + 8 ≤ (sp - 9).toNat + 289
        omega

end K256.Proofs.Sec1.Serialize
