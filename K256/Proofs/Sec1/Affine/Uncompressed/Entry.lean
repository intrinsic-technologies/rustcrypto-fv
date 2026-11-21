import K256.Proofs.Sec1.LIR.Fn11f780
import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

def saved (args : Values Value Reg.count) (m : Ram) (sp : Word) : Ram :=
  let m := memStore m (sp - 8) (args[5].get 64)
  let m := memStore m (sp - 16) (args[15].get 64)
  let m := memStore m (sp - 24) (args[14].get 64)
  let m := memStore m (sp - 32) (args[13].get 64)
  let m := memStore m (sp - 40) (args[12].get 64)
  let m := memStore m (sp - 48) (args[3].get 64)
  memStore m (sp - 56) (args[7].get 64)

def choiceResume (target : Label) (address : Word) (arity : Reg.count = signature target) :
    StackFrame Value Label signature Reg.count :=
  {target, kept := #v[], arity, guard := some ⟨64, address⟩}

private theorem writableStack {m : Ram} {code : CodeMap} {sp delta : Word}
    (win : Writable code m (sp - 273) 273) (h : ((0 - delta) - (0 - 273)).toNat + 8 ≤ 273) :
    Writable code m (sp - delta) 8 :=
  win.of_offsets (addr_sub _ _) (addr_sub _ _) h

private theorem writeGuard {m : Ram} {code : CodeMap} {addr base pc : Word} {len : Nat}
    {bytes : List UInt8} (w : Writable code m addr 8)
    (cover : ∀ v ∈ codeRange base bytes, v ∈ code)
    (within : (pc - base).toNat + len ≤ bytes.length) : StoreOk code m addr 8 pc len := by
  have hs := K256.Proofs.ParseSignature.storeOk_of_codeRange w cover within
  have ha : base + BitVec.ofNat 64 (pc - base).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rwa [ha] at hs

private theorem coordinateRead {m : Ram} {p off : Word} (win : Readable m p 32)
    (h : off.toNat + 8 ≤ 32) : LoadOk m (p + off) 8 :=
  LoadOk.of_offsets win rfl (BitVec.add_zero p).symm (by simpa using h)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem firstChoice (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp x : Word) (rsp : args[4].get 64 = sp) (rsi : args[6].get 64 = x)
    (win : Writable code mem (sp - 273) 273) (src : Readable mem x 32)
    (cover : ∀ v ∈ codeRange 0x11f780 bytes_l11f780, v ∈ code) :
    let m := saved args mem sp
    let a := bswapSpec (memLoad m x 64)
    let b := bswapSpec (memLoad m (x + 8) 64)
    let c := bswapSpec (memLoad m (x + 16) 64)
    let d := bswapSpec (memLoad m (x + 24) 64)
    ∃ regs, program.runBlock (dialect code) ⟨.l11f780, args, mem⟩ =
        .call ⟨.l127d50, regs, memStore m (sp - 272) (0x11f825 : Word)⟩
          (choiceResume .l11f825 0x11f825 rfl) ∧
      regs[7].get 64 = BitVec.ofNat 64 (invalid a b c d).toNat ∧
      regs[4].get 64 = sp - 272 ∧ regs[3].get 64 = args[2].get 64 ∧
      regs[5].get 64 = a >>> 16 ∧ regs[12].get 64 = shldResult 12 c d &&& 0xfffffffffffff ∧
      regs[13].get 64 = d &&& 0xfffffffffffff ∧
      regs[14].get 64 = shldResult 36 a b ∧ regs[15].get 64 = shldResult 24 b c ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → regs[i] = args[i]) := by
  dsimp only
  refine ⟨?regs, ?eval, ?rest⟩
  case eval =>
    cfg_eval [rsp, rsi]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | apply writeGuard _ cover (by decide +kernel)
          apply writableStack (sp := sp) _ (by decide)
          repeat' apply Writable.memStore
          exact win
        | apply LoadOk.of_region (b := x) (len := 32) _ (Nat.le_refl _) (by omega)
          repeat' apply Readable.memStore
          exact src
        | apply coordinateRead (p := x) _ (by decide)
          repeat' apply Readable.memStore
          exact src)
    rfl
  case rest =>
    refine ⟨?flag, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?kept⟩
    case kept =>
      intro ⟨i, _⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    case flag =>
      change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
      simp only [setWidth_mergeGPR8, cmpAbove, orFlags, Option.getD_some, beq_iff_eq,
        decide_eq_true_eq, invalid, saved]
      exact flagByte _ _

theorem saved_frame (args : Values Value Reg.count) (mem : Ram) (sp : Word)
    (room : 273 ≤ sp.toNat) :
    RamWriteFrame mem (saved args mem sp) [⟨(sp - 273).toNat, 273⟩] := by
  have slot (k : Word) (hk : 8 ≤ k.toNat ∧ k.toNat ≤ 273) :
      InRegions [⟨(sp - 273).toNat, 273⟩] (sp - k) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (sp - 273).toNat ≤ (sp - k).toNat ∧
      (sp - k).toNat + 8 ≤ (sp - 273).toNat + 273 ∧ (sp - k).toNat + 8 ≤ 2^64
    bv_omega
  unfold saved
  repeat' (refine RamWriteFrame.memStore ?_ _ (slot _ (by decide)))
  apply RamWriteFrame.refl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem secondChoice (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp y : Word) (rsp : args[4].get 64 = sp) (rbx : args[3].get 64 = y)
    (win : Writable code mem (sp - 8) 224) (src : Readable mem y 32)
    (cover : ∀ v ∈ codeRange 0x11f831 bytes_l11f831, v ∈ code) :
    let bit := ((args[0].get 64).setWidth 8).setWidth 64
    let m := memStore mem (sp + 200) bit
    let m := memStore m (sp + 80) (args[13].get 64 &&& -bit)
    let m := memStore m (sp + 48) (args[12].get 64 &&& -bit)
    let m := memStore m (sp + 32) (args[5].get 64 &&& -bit)
    let a := bswapSpec (memLoad m y 64)
    let b := bswapSpec (memLoad m (y + 8) 64)
    let c := bswapSpec (memLoad m (y + 16) 64)
    let mask := -bit &&& 0xfffffffffffff
    let m := memStore m (sp + 88) (args[15].get 64 &&& mask)
    let d := bswapSpec (memLoad m (y + 24) 64)
    let m := memStore m (sp + 56) (mask &&& args[14].get 64)
    ∃ regs, program.runBlock (dialect code) ⟨.l11f831, args, mem⟩ =
        .call ⟨.l127d50, regs, memStore m (sp - 8) (0x11f8ea : Word)⟩
          (choiceResume .l11f8ea 0x11f8ea rfl) ∧
      regs[7].get 64 = BitVec.ofNat 64 (invalid a b c d).toNat ∧
      regs[4].get 64 = sp - 8 ∧ regs[5].get 64 = 0xfffffffffffff ∧
      regs[3].get 64 = shldResult 36 a b ∧ regs[12].get 64 = shldResult 24 b c ∧
      regs[13].get 64 = shldResult 12 c d &&& 0xfffffffffffff ∧
      regs[14].get 64 = a >>> 16 ∧ regs[15].get 64 = d &&& 0xfffffffffffff ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → regs[i] = args[i]) := by
  dsimp only
  refine ⟨?regs, ?eval, ?rest⟩
  case eval =>
    cfg_eval [rsp, rbx]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | apply writeGuard _ cover (by decide +kernel)
          first
            | refine Writable.of_offsets (x := sp) (b := sp - 8) (d := 0 - 8) (len := 224) ?_ rfl (addr_sub _ _) (by decide)
            | refine Writable.of_offsets (x := sp) (b := sp - 8) (d := 0 - 8) (len := 224) ?_ (addr_sub _ _) (addr_sub _ _) (by decide)
          repeat' apply Writable.memStore
          exact win
        | apply LoadOk.of_region (b := y) (len := 32) _ (Nat.le_refl _) (by omega)
          repeat' apply Readable.memStore
          exact src
        | apply coordinateRead (p := y) _ (by decide)
          repeat' apply Readable.memStore
          exact src)
    rfl
  case rest =>
    refine ⟨?flag, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?kept⟩
    case kept =>
      intro ⟨i, _⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    case flag =>
      change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
      simp only [setWidth_mergeGPR8, cmpAbove, orFlags, Option.getD_some, beq_iff_eq,
        decide_eq_true_eq, invalid]
      exact flagByte _ _

end K256.Proofs.Sec1.Affine.Uncompressed
