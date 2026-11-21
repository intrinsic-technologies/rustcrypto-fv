import K256.Proofs.Signing.Nonce.Fill.Memory
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

private theorem jump {l l' : Label} {a b : Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l, a, m⟩ = .jump ⟨l', b, n⟩) :
    Reaches l a m l' b n := by
  apply Semantics.Reaches.single
  change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
  rw [run]
  rfl

private def prologueMemory (fr : Activation) : Ram :=
  let m := memStore fr.original (fr.rsp - 8) fr.rbp
  let m := memStore m (fr.rsp - 16) fr.r15
  let m := memStore m (fr.rsp - 24) fr.r14
  let m := memStore m (fr.rsp - 32) fr.r13
  let m := memStore m (fr.rsp - 40) fr.r12
  let m := memStore m (fr.rsp - 48) fr.rbx
  memStore m (fr.rsp - 192) fr.rsi

private def configuredMemory (fr : Activation) : Ram :=
  let m := memStore (prologueMemory fr) (fr.rsp - 176) (256#32)
  let m := memStore m (fr.rsp - 88) fr.rdi
  let m := memStore m (fr.rsp - 96) (fr.rdi + 40)
  let m := memStore m (fr.rsp - 168) (fr.rdi + 8)
  memStore m (fr.rsp - 184) (32#64)

private theorem slotInStack {fr : Activation} (env : Environment fr) {extra : List MemoryRegion}
    (off : BitVec 64) (n : Nat) (bounds : n ≤ off.toNat ∧ off.toNat ≤ 2160) :
    InRegions (fr.region :: extra) (fr.rsp - off) n := by
  refine ⟨fr.region, .head _, ?_⟩
  change fr.low.toNat ≤ (fr.rsp - off).toNat ∧
    (fr.rsp - off).toNat + n ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧
    (fr.rsp - off).toNat + n ≤ 2^64
  rw [env.low, env.subNat 2160 (by decide), env.subNat off bounds.2]
  simp only [BitVec.reduceToNat]
  have := env.depth
  have := env.limit
  omega

private theorem configuredWrites {fr : Activation} (env : Environment fr) (extra : List MemoryRegion) :
    RamWriteFrame fr.original (configuredMemory fr) (fr.region :: extra) := by
  unfold configuredMemory prologueMemory
  iterate 12 apply RamWriteFrame.memStore _ _ (slotInStack env _ _ (by decide))
  exact .refl _ _

private theorem stackSlot {fr : Activation} (env : Environment fr)
    {m : Ram} (stack : Writable Extracted.programImage m (fr.rsp - 2160) 2160)
    (off : BitVec 64) (n : Nat) (bounds : n ≤ off.toNat ∧ off.toNat ≤ 2160) :
    Writable Extracted.programImage m (fr.rsp - off) n := by
  apply stack.sub <;>
    rw [env.subNat 2160 (by decide), env.subNat off bounds.2] <;>
    simp only [BitVec.reduceToNat] <;> (have := env.depth; omega)

private theorem storeGuard {m : Ram} {addr pc base : BitVec 64} {size len : Nat} {bytes : List UInt8}
    (writable : Writable Extracted.programImage m addr size)
    (included : ∀ x ∈ codeRange base bytes, x ∈ fnCode)
    (within : (pc - base).toNat + len ≤ bytes.length) :
    StoreOk Extracted.programImage m addr size pc len := by
  have h := ParseSignature.storeOk_of_codeRange writable
    (fun x hx => Common.fnCode_subset_programImage x (included x hx)) within
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show base + (pc - base) = pc by bv_omega] at h

private abbrev keptRegisters : List Nat := [2, 5, 6, 8, 9, 14, 15, 22, 39, 50, 51]

private theorem prologue {fr : Activation} {a : Registers} (env : Environment fr)
    (stack : Writable Extracted.programImage fr.original (fr.rsp - 2160) 2160)
    (rsp : a[4].get 64 = fr.rsp) (dx : a[2].get 64 = 32)
    (bx : a[3].get 64 = fr.rbx) (bp : a[5].get 64 = fr.rbp) (si : a[6].get 64 = fr.rsi)
    (di : a[7].get 64 = fr.rdi) (r12 : a[12].get 64 = fr.r12) (r13 : a[13].get 64 = fr.r13)
    (r14 : a[14].get 64 = fr.r14) (r15 : a[15].get 64 = fr.r15) :
    ∃ b, Reaches .l100a40 a fr.original .l100a6a b (prologueMemory fr) ∧
      b[4] = ⟨64, sp fr⟩ ∧ b[1] = ⟨64, fr.rdi + 8⟩ ∧ b[7].get 64 = fr.rdi ∧
      b[13] = ⟨64, 32⟩ ∧ ∀ i : Fin Reg.count, i.val ∈ keptRegisters → b[i] = a[i] := by
  refine ⟨?_, ?step, ?regs⟩
  case step =>
    apply jump
    cfg_eval [rsp, dx, bx, bp, si, di, r12, r13, r14, r15, reduceAddOffset, cmpSpec, subSpec]
    iterate 7
      refine Eq.trans (ite_eq_left ?_) ?_
      apply storeGuard _ code_l100a40 (by decide +kernel)
      repeat' apply Writable.memStore
      exact stackSlot env stack _ _ (by decide)
    rfl
  case regs =>
    refine ⟨rfl, rfl, di, rfl, ?_⟩
    rintro ⟨i, _⟩ hi
    simp only [keptRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem branchToHead (a : Registers) (m : Ram) :
    Reaches .l100aab a m .l100ab0 a m := by
  apply jump
  cfg_eval
  congr 2
  have ext {u v : Registers} (same : ∀ j : Fin 53, u[j.val] = v[j.val]) : u = v :=
    Vector.ext fun i hi => same ⟨i, hi⟩
  apply ext
  intro j
  finite_cases j <;> rfl

private theorem configure {fr : Activation} {a : Registers} (env : Environment fr)
    (stack : Writable Extracted.programImage fr.original (fr.rsp - 2160) 2160)
    (rsp : a[4] = ⟨64, sp fr⟩) (cx : a[1] = ⟨64, fr.rdi + 8⟩) (di : a[7].get 64 = fr.rdi)
    (r13 : a[13] = ⟨64, 32⟩) :
    ∃ b, Reaches .l100a6a a (prologueMemory fr) .l100aab b (configuredMemory fr) ∧
      b[4] = ⟨64, sp fr⟩ ∧ b[1].width = 64 ∧ b[7] = ⟨64, fr.rdi + 8⟩ ∧
      b[12] = ⟨64, fr.rdi + 40⟩ ∧ b[13].width = 64 ∧ b[3] = ⟨64, 0x12a820⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ keptRegisters → b[i] = a[i] := by
  have cxBits := congrArg (Value.get 64) cx
  have rspBits := congrArg (Value.get 64) rsp
  have sizeBits := congrArg (Value.get 64) r13
  refine ⟨?_, ?step, ?regs⟩
  case step =>
    apply jump
    cfg_eval [rspBits, cxBits, di, sizeBits, sp, reduceAddOffset, prologueMemory, configuredMemory]
    segment_words []
    iterate 5
      refine Eq.trans (ite_eq_left ?_) ?_
      apply storeGuard _ code_l100a6a (by decide +kernel)
      repeat' apply Writable.memStore
      exact stackSlot env stack _ _ (by decide)
    refine Eq.trans (ite_eq_left ?_) ?_
    · apply LoadOk.of_region _ (Nat.le_refl _) (Nat.le_refl _)
      repeat' apply Readable.memStore
      exact (stackSlot env stack _ _ (by decide)).readable
    rw [ite_eq_right (by decide : (32 : BitVec 64) ≠ 0)]
    rfl
  case regs =>
    refine ⟨rsp, congrArg Value.width cx, rfl, rfl, congrArg Value.width r13, rfl, ?_⟩
    rintro ⟨i, _⟩ hi
    simp only [keptRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem entryPath {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    (entry : Atom.All Extracted.programImage a fr.original (Fn100a40.frameAt .l100a40 fr))
    (seed : StateAt fr.original (fr.rdi + 8) state) :
    ∃ b m, Reaches .l100a40 a fr.original .l100ab0 b m ∧ Head fr state b m := by
  simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at entry
  obtain ⟨rsp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ft, fc,
    retRead, ret, retLow, stack, room, align, readD0, gotD0, readE0, gotE0,
    read10, got10, read20, got20, apart, _⟩ := entry
  have dx32 : a[2].get 64 = 32 := (congrArg (Value.get 64) dx).trans env.size
  have rspBits : a[4].get 64 = fr.rsp := congrArg (Value.get 64) rsp
  have bxBits : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have bpBits : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have siBits : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have diBits : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have r12Bits : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have r13Bits : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have r14Bits : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have r15Bits : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  obtain ⟨b, first, b4, b1, b7, b13, firstKept⟩ :=
    prologue env stack rspBits dx32 bxBits bpBits siBits diBits r12Bits r13Bits r14Bits r15Bits
  obtain ⟨c, rest, c4, c1, c7, c12, c13, c3, restKept⟩ := configure env stack b4 b1 b7 b13
  have kept (i : Fin Reg.count) (hi : i.val ∈ keptRegisters) : c[i] = a[i] :=
    (restKept i hi).trans (firstKept i hi)
  refine ⟨c, configuredMemory fr, first.trans (rest.trans (branchToHead c _)), ?_⟩
  have writes := configuredWrites env []
  have depth := env.depth
  have low := env.limit
  have bottom : fr.low.toNat = fr.rsp.toNat - 2160 := by rw [env.low, env.subNat 2160 (by decide)]; rfl
  have outside (p : BitVec 64) (n : Nat) (bound : p.toNat + n ≤ 2^64)
      (disj : p.toNat + n ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ p.toNat) :
      Outside [fr.region] p n := by
    refine ⟨bound, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change p.toNat + n ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ p.toNat
    omega
  have preserve (p : BitVec 64) (bound : p.toNat + 8 ≤ 2^64)
      (disj : p.toNat + 8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ p.toNat) :
      memLoad (configuredMemory fr) p 64 = memLoad fr.original p 64 :=
    writes.memLoad_eq (outside p 8 bound disj)
  have statePtr : fr.rdi + 8 = fr.rsp + 704 := by rw [env.gen]; bv_omega
  have stateOutside : Outside [fr.region] (fr.rdi + 8) 64 := by
    rw [statePtr]
    apply outside
    · rw [env.addNat 704 (by decide)]
      simp only [BitVec.reduceToNat]
      omega
    · right
      rw [env.addNat 704 (by decide)]
      simp only [BitVec.reduceToNat]
      omega
  refine ⟨?_, stateAfter writes stateOutside seed, c7, c12, c3⟩
  · refine ⟨?atoms, ?widths, ?bits, ?state, ?value, configuredWrites env _⟩
    case atoms =>
      change Atom.All _ _ _ (Fn100a40.frameAt .l100ac0 fr)
      simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds]
      have got (p : BitVec 64) (start : 0x203dd0 ≤ p.toNat) (finish : p.toNat + 8 ≤ 0x203e28) :
          memLoad (configuredMemory fr) p 64 = memLoad fr.original p 64 :=
        preserve p (by omega) (by omega)
      have gotD0' := (got 0x203dd0 (by decide) (by decide)).trans gotD0
      have gotE0' := (got 0x203de0 (by decide) (by decide)).trans gotE0
      have got10' := (got 0x203e10 (by decide) (by decide)).trans got10
      have got20' := (got 0x203e20 (by decide) (by decide)).trans got20
      refine ⟨c4, (kept 22 (by decide)).trans df, (kept 39 (by decide)).trans mx,
        (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        retRead.of_frame writes, (preserve fr.rsp (by omega) (Or.inr (by omega))).trans ret, retLow,
        stack.of_frame writes, room, align, readD0.of_frame writes, gotD0', readE0.of_frame writes,
        gotE0', read10.of_frame writes, got10', read20.of_frame writes, got20', apart, trivial⟩
      all_goals unfold configuredMemory prologueMemory; segment_words [] <;> exact env.size.symm
    case widths =>
      rintro ⟨i, _⟩ hi
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact c1
      · exact congrArg Value.width ((kept 2 (by decide)).trans dx)
      · exact congrArg Value.width c3
      · exact congrArg Value.width c4
      · exact congrArg Value.width ((kept 5 (by decide)).trans bp)
      · exact congrArg Value.width ((kept 6 (by decide)).trans si)
      · exact congrArg Value.width c7
      · exact congrArg Value.width ((kept 8 (by decide)).trans r8)
      · exact congrArg Value.width ((kept 9 (by decide)).trans r9)
      · exact congrArg Value.width c12
      · exact c13
      · exact congrArg Value.width ((kept 14 (by decide)).trans r14)
      · exact congrArg Value.width ((kept 15 (by decide)).trans r15)
    case bits => unfold configuredMemory sp; segment_words []
    case state => unfold configuredMemory sp; segment_words []
    case value => unfold configuredMemory sp; segment_words []

end K256.Proofs.Signing.Nonce.Fill
