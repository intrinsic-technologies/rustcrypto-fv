import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Prepare
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.PreviousCopy

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem preparationWrites (s : RamState) :
    StackWrites (preparationComponents s) (stackPtr s) [(8,8), (264,8), (272,144)] := by
  intro c member a covers
  simp only [preparationComponents, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact covers.elim
    | exact ⟨(8,8), by decide, covers⟩
    | exact ⟨(264,8), by decide, covers⟩
    | exact ⟨(272,144), by decide, covers⟩

private theorem preparationFrame {entry s t : RamState}
    (stack : Stack.Valid entry 2264) (sp : stackPtr s = Counter.base entry)
    (agreement : AgreesExcept (preparationComponents s) s t) :
    MemoryWriteFrame s t #v[Stack.region entry 2264] := by
  apply agreement.memoryWriteFrame
  intro c member a covers
  obtain ⟨⟨off,len⟩, inside, place⟩ := preparationWrites s c member a covers
  have fit : off + len ≤ 536 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with h | h | h
    all_goals exact congrArg (fun p : Nat × Nat => p.1 + p.2) h ▸ (by decide)
  rw [sp, Counter.base_add (by omega)] at place
  exact ⟨Stack.region entry 2264, by simp,
    stackRegion_contains_sub stack.2.2.1 (by omega) (by omega) place⟩

private theorem preserveSlots {s t : RamState} {components : List Component}
    {ranges : List (Nat × Nat)} {offsets : List Nat}
    (writes : StackWrites components (stackPtr s) ranges)
    (agreement : AgreesExcept components s t) (sp : stackPtr t = stackPtr s)
    (within : ∀ r ∈ ranges, r.1 + r.2 ≤ 2^64)
    (apart : ∀ off ∈ offsets, off + 8 ≤ 2^64 ∧
      ∀ r ∈ ranges, off + 8 ≤ r.1 ∨ r.1 + r.2 ≤ off) :
    ∀ i ∈ offsets.map (BitVec.ofNat 64), slot t i = slot s i := by
  intro i member
  obtain ⟨off, inOffsets, rfl⟩ := List.mem_map.mp member
  change memLoad t.external (stackPtr t + _) 64 = _
  rw [sp]
  exact agrees_memLoad (writes.agrees agreement (apart off inOffsets).1 within
    (apart off inOffsets).2)

private theorem previousCopyPre [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat}
    (ctx : Counter.StackContext entry boundary length) (saved : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f682) (rbx : s.regValue .rbx = 0) : PreviousCopy.CopyPre s := by
  have sp : rspOf s = Counter.base entry := saved.sp
  have read (off : Nat) (bound : off ≤ 536) (fit : off + 8 ≤ 544) :
      MemReadable s (rspOf s + BitVec.ofNat 64 off) 8 := by
    rw [sp]
    exact Counter.read_stack ctx saved.toRunning bound fit
  have write (off : Nat) (bound : off ≤ 536) (align : off % 8 = 0) :
      MemWritable s (rspOf s + BitVec.ofNat 64 off) 8 := by
    rw [sp, Counter.base_add bound]
    exact stack_writable8 ctx.stack ctx.stackAvoid saved.allocated (by omega) (by omega)
  have apart (off size : Nat) (bound : off ≤ 536) (fit : off + size ≤ 544) :
      RangeApart (rspOf s + BitVec.ofNat 64 off) size 0x10f682 65 := by
    rw [sp]
    exact Counter.stack_apart ctx (codeOff := 0xf682) bound fit (by decide)
  refine ⟨pc, rbx, ?_, ?_, ?_, ?_, apart 335 1 (by decide) (by decide)⟩
  · intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact read 456 (by decide) (by decide)
    · exact read 464 (by decide) (by decide)
    · exact read 472 (by decide) (by decide)
    · exact read 480 (by decide) (by decide)
  · intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact write 272 (by decide) (by decide)
    · exact write 280 (by decide) (by decide)
    · exact write 288 (by decide) (by decide)
    · exact write 296 (by decide) (by decide)
  · intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact apart 272 8 (by decide) (by decide)
    · exact apart 280 8 (by decide) (by decide)
    · exact apart 288 8 (by decide) (by decide)
    · exact apart 296 8 (by decide) (by decide)
  · rw [sp]
    exact Counter.write_byte ctx saved.toRunning (off := 335) (by decide)

private theorem previousCopyWrites (s : RamState) :
    StackWrites [.reg 1, .reg 0, .reg 3, .mem (rspOf s + 296) 8, .mem (rspOf s + 288) 8,
      .mem (rspOf s + 280) 8, .mem (rspOf s + 272) 8, .mem (rspOf s + 335) 1,
      .flags, .rip] (stackPtr s) [(296,8), (288,8), (280,8), (272,8), (335,1)] := by
  intro c member a covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covers.elim
  · exact covers.elim
  · exact covers.elim
  · exact ⟨(296,8), by decide, covers⟩
  · exact ⟨(288,8), by decide, covers⟩
  · exact ⟨(280,8), by decide, covers⟩
  · exact ⟨(272,8), by decide, covers⟩
  · exact ⟨(335,1), by decide, covers⟩
  · exact covers.elim
  · exact covers.elim

private theorem previous_digest [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {length n : Nat}
    (head : LoopState entry s boundary key info length n) (positive : 0 < n)
    (sp : stackPtr t = stackPtr s)
    (agreement : AgreesExcept (preparationComponents s) s t) :
    (⟨(stackPtr t + 456).toNat, 32⟩ : MemoryRegion).HasBytes t.external
      (blocks .sha256 key info n).2 := by
  have size := blocks_sha256_previous_size key info positive
  have same := (preparationWrites s).agrees agreement (off := 456) (len := 32)
    (by decide) (by decide) (by decide)
  refine ⟨size, fun i => ?_⟩
  have within : i.val < 32 := size ▸ i.isLt
  have source := head.previous.2 i
  change s.external[BitVec.ofNat 64 ((s.regValue .rsp + 456).toNat + i.val)]? = _ at source
  rw [← stackPtr_eq_regValue_rsp s, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at source
  change t.external[BitVec.ofNat 64 ((stackPtr t + 456).toNat + i.val)]? = _
  rw [sp, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact (same i.val within).trans source

theorem startInfo [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (head : LoopState entry s boundary key info length n)
    (more : 32*n < length) (bound : length ≤ 8160) :
    ∃ t, SavedFrame entry t boundary length ∧ t.RIP = 0x10f6c3 ∧
      HmacAt t (stackPtr t + 272) key (blocks .sha256 key info n).2 ∧
      t.regValue .r12 = 0x10dd60 ∧
      t.regValue .r15 = entry.regValue .rcx + BitVec.ofNat 64 (32*n) ∧
      slot t 8 = BitVec.ofNat 64 (length - 32*n) ∧
      slot t 264 = BitVec.ofNat 64 (min (length - 32*n) 32) ∧
      (∀ i ∈ ([224,232,240,248,256,416,424,440] : List (BitVec 64)), slot t i = slot s i) ∧
      MemoryWriteFrame s t #v[Stack.region entry 2264] := by
  obtain ⟨u, savedU, pcU, bxU, hmacU, remainingU, chunkU, preservesU⟩ :=
    prepareRound pre head more bound
  have spU : stackPtr u = stackPtr s := preservesU.read (r := 4) (n := 64)
    (by simp [preparationComponents])
  have keepU := preserveSlots (preparationWrites s) preservesU spU
    (offsets := [224,232,240,248,256,416,424,440]) (by decide) (by decide)
  have frameU := preparationFrame pre.call.stack head.sp preservesU
  have memcpyU : u.regValue .r12 = 0x10dd60 :=
    (preservesU.read (r := 12) (n := 64) (by simp [preparationComponents])).trans head.memcpy
  have outputReg : u.regValue .r15 = s.regValue .r15 :=
    preservesU.read (r := 15) (n := 64) (by simp [preparationComponents])
  have outputU : u.regValue .r15 = entry.regValue .rcx + BitVec.ofNat 64 (32*n) := by
    rw [outputReg, head.outputPtr, Nat.min_eq_left (Nat.le_of_lt more)]
  by_cases first : n = 0
  · exact ⟨u, savedU, by simpa only [first, ↓reduceIte] using pcU,
      by simpa only [first, blocks_zero] using hmacU,
      memcpyU, outputU, remainingU, chunkU, keepU, frameU⟩
  · have pos : 0 < length := by omega
    have ctx := Counter.StackContext.of_pre pre pos bound
    have copyPre := previousCopyPre ctx savedU (by simpa only [first, ↓reduceIte] using pcU) (bxU first)
    have digest := previous_digest head (by omega) spU preservesU
    obtain ⟨fuel, t, run, ready, pc, hmac, preserves⟩ := previousCopy
      (supportedMachine_readyToStep savedU.machine) savedU.loaded ctx.outside copyPre hmacU digest
    have writes := previousCopyWrites u
    obtain ⟨saved, frame⟩ :=
      writes.saved pre pos bound savedU run ready preserves (by decide) (by simp)
    have sp : stackPtr t = stackPtr u := preserves.read (r := 4) (n := 64) (by simp)
    have keep := preserveSlots writes preserves sp
      (offsets := [8,264,224,232,240,248,256,416,424,440]) (by decide) (by decide)
    exact ⟨t, saved, pc, hmac,
      (preserves.read (r := 12) (n := 64) (by simp)).trans memcpyU,
      (preserves.read (r := 15) (n := 64) (by simp)).trans outputU,
      (keep 8 (by decide)).trans remainingU, (keep 264 (by decide)).trans chunkU,
      fun i hi => (keep i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))).trans (keepU i hi),
      memoryWriteFrame_trans frameU frame⟩

end Hkdf.Proofs.NewExpand.Expand
