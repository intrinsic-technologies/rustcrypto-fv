import K256.Proofs.Generate.Generator.Multiply.Caller.TableCopies
import K256.Proofs.Generate.Generator.Affine.Select.Setup
import K256.Proofs.Generate.LIR.Fn10ee80.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def firstCopySaved (fr : Activation) : Ram :=
  let m := memStore fr.original (fr.rsp - 8) fr.r15
  let m := memStore m (fr.rsp - 16) fr.r14
  let m := memStore m (fr.rsp - 24) fr.r13
  let m := memStore m (fr.rsp - 32) fr.r12
  let m := memStore m (fr.rsp - 40) fr.rbx
  memStore m (fr.rsp - 4136) (0 : BitVec 64)

def firstCopyRecord (fr : Activation) : Ram :=
  let sp := fr.rsp - 5960
  let m := memCopy (firstCopySaved fr) (sp + 8) 0x202bc8 120
  let m := memStore m (sp + 152) (memLoad fr.original (fr.rsi + 24) 64)
  let m := memStore m (sp + 144) (memLoad fr.original (fr.rsi + 16) 64)
  let m := memStore m (sp + 136) (memLoad fr.original (fr.rsi + 8) 64)
  memStore m (sp + 128) (memLoad fr.original fr.rsi 64)

def firstCopyMemory (fr : Activation) : Ram :=
  let sp := fr.rsp - 5960
  memCopy (memStore (firstCopyRecord fr) (sp - 8) (0x10ef08 : BitVec 64)) (sp + 3848) (sp + 8) 152

theorem generatorBytes (i : Nat) (h : i < 120) :
    ∃ b, ((0x202bc8 : BitVec 64) + BitVec.ofNat 64 i, b) ∈ Extracted.programImage := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  apply exists_mem_toCodeMap (s := sec) (by simp [sec, Extracted.programSections])
  · change 0x200000 ≤ ((0x202bc8 : BitVec 64) + BitVec.ofNat 64 i).toNat
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  · change ((0x202bc8 : BitVec 64) + BitVec.ofNat 64 i).toNat < 0x200000 + Extracted.rodataBytes.size
    rw [Common.rodataBytes_size]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega

set_option maxRecDepth 4096 in
private theorem firstCopyCall {fr : Activation} {a : Registers}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (src : fr.rsi = fr.rsp + 8) (source : Readable fr.original fr.rsi 32) :
    let sp := fr.rsp - 5960
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10ee80, a, fr.original⟩ =
        .call ⟨.l12a820, b, memStore (firstCopyRecord fr) (sp - 8) (0x10ef08 : BitVec 64)⟩
          (callFrame .l10ef08 0x10ef08) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 3848 ∧ b[6].get 64 = sp + 8 ∧
      b[2].get 64 = 152 ∧ b[3] = ⟨64, fr.rdi⟩ ∧ b[13] = ⟨64, 0x12a820⟩ ∧
      b[14] = ⟨64, sp + 3848⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,9,10,11,12,15,22,39,50,51] → b[i] = a[i] := by
  dsimp only
  simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, _, _, bx, _, si, di, _, _, t12, t13, t14, t15, _, _, _, _, _, _, stack, _⟩ := atoms
  have sp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) rsp
  have direction : a[22].get 1 = 0 := congrArg (Value.get 1) df
  have bx' : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have si' : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have di' : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have r12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) t12
  have r13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) t13
  have r14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) t14
  have r15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) t15
  have dest : Writable Extracted.programImage fr.original (fr.rsp - 5960 + 8) 120 := by slot_state region
  obtain ⟨readable, apart⟩ := Affine.readableCodeSpan (n := 120) (base := 0x202bc8) generatorBytes image (by decide) (by decide) dest (by decide)
  have repGuard : RepMovsOk Extracted.programImage (firstCopySaved fr) 0 0x202bc8
      (fr.rsp - 5960 + 8) 15 8 0x10eeb9 3 := by
    have w : StoreOk Extracted.programImage (firstCopySaved fr) (fr.rsp - 5960 + 8) 120 0x10eeb9 3 := by
      have ww : Writable Extracted.programImage (firstCopySaved fr) (fr.rsp - 5960 + 8) 120 := by
        unfold firstCopySaved
        repeat apply Writable.memStore
        exact dest
      slot_guard using code_l10ee80
    have r : Readable (firstCopySaved fr) 0x202bc8 120 := by
      unfold firstCopySaved
      repeat apply Readable.memStore
      exact readable
    exact ⟨rfl, r.low, w.low, r.present, w.present, apart, w.tables, w.apart, w.notCode⟩
  rw [src] at source
  unfold firstCopyRecord firstCopySaved
  unfold firstCopySaved at repGuard
  generalize hm : fr.original = m at stack source repGuard ⊢
  refine ⟨?_, ?run, ?post⟩
  case run =>
    generate_block [sp, direction, bx', si', di', r12, r13, r14, r15, src]
    segment_words [src, memCopy]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10ee80)
    have addr : fr.rsp - 5960 + 8 = fr.rsp - 5952 := by bv_omega
    rw [addr] at repGuard
    refine Eq.trans (ite_eq_left (Or.inr repGuard)) ?_
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10ee80)
    rfl
  case post =>
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · change fr.rsp - 5968 = fr.rsp - 5960 - 8
      bv_omega
    · change fr.rsp - 2112 = fr.rsp - 5960 + 3848
      bv_omega
    · change fr.rsp - 5952 = fr.rsp - 5960 + 8
      bv_omega
    · change Value.mk 64 (fr.rsp - 2112) = _
      congr 1 <;> bv_omega
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem firstCopy {fr : Activation} {a : Registers}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (src : fr.rsi = fr.rsp + 8) (source : Readable fr.original fr.rsi 32) :
    let sp := fr.rsp - 5960
    ∃ b, Reaches .l10ee80 a fr.original .l10ef08 b (firstCopyMemory fr) ∧
      b[4] = ⟨64, sp⟩ ∧ b[3] = ⟨64, fr.rdi⟩ ∧ b[13] = ⟨64, 0x12a820⟩ ∧
      b[14] = ⟨64, sp + 3848⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,9,10,11,12,15,22,39,50,51] → b[i] = a[i] := by
  dsimp only
  obtain ⟨b, call, hsp, dst, ptr, n, bx, target, recPtr, keep⟩ := firstCopyCall atoms image src source
  simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, df, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, _⟩ := atoms
  have w : Writable Extracted.programImage (firstCopyRecord fr) (fr.rsp - 5960 - 8) 5928 := by
    unfold firstCopyRecord firstCopySaved memCopy
    repeat apply Writable.memStore
    slot_state region
  have direction : b[22].get 1 = 0 := congrArg (Value.get 1) ((keep 22 (by decide)).trans df)
  obtain ⟨c, run, top, saved⟩ := stackCopy (sp := fr.rsp - 5960) (dst := 3848) (src := 8)
    (n := 152) w (by decide) (by decide) (by decide) (by decide) (by decide) call hsp dst ptr n direction
  refine ⟨c, run, top, (saved 3 (by decide)).trans bx, (saved 13 (by decide)).trans target,
    (saved 14 (by decide)).trans recPtr, fun i hi => (saved i ?_).trans (keep i hi)⟩
  simp only [memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
  omega

end K256.Proofs.Generate.Generator.Multiply.Caller
