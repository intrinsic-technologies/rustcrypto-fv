import K256.Proofs.Sec1.Parser.Result.Blocks
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Sec1.Parser.Control
import K256.Proofs.Sec1.Parser.Affine
import K256.Proofs.Sec1.Parser.LengthTable
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Sec1.Parser.Result

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

variable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}

private theorem copyGuard {src dst pc : BitVec 64} {df : BitVec 1}
    (forward : df = 0) (read : Readable mem src 88)
    (write : StoreOk code mem dst 88 pc 3)
    (apart : src.toNat + 88 ≤ dst.toNat ∨ dst.toNat + 88 ≤ src.toNat) :
    RepMovsOk code mem df src dst 11 8 pc 3 :=
  ⟨forward, read.low, write.low, read.present, write.present, apart, write.tables, write.apart, write.notCode⟩

def resultStore (mem : Ram) (sp out : BitVec 64) (flag : BitVec 8) : Ram :=
  let staged := memCopy mem (sp + 72) (sp + 160) 88
  let selected := memStore staged (sp + 160) flag
  if flag = 0 then selected else memCopy selected (out + 8) (sp + 72) 88

theorem afterAffine (hcode : ∀ x ∈ fnCode, x ∈ code)
    (sp out : BitVec 64) (tag affine identity : BitVec 8)
    (rsp : args[4].get 64 = sp) (src : args[3].get 64 = sp + 160)
    (dst : args[15].get 64 = out) (r12 : (args[12].get 64).setWidth 8 = identity)
    (df : args[22].get 1 = 0) (valid : validTag tag)
    (tagByte : memLoad mem (sp + 4) 8 = tag) (affineByte : memLoad mem (sp + 248) 8 = affine)
    (stack : Writable code mem sp 249) (output : Writable code mem (out + 8) 88)
    (apart : (sp + 72).toNat + 88 ≤ (out + 8).toNat ∨ (out + 8).toNat + 88 ≤ (sp + 72).toNat) :
    let flag := selectedByte tag affine identity
    ∃ next : Values Value Reg.count,
      Reaches code .l1064f4 args mem (if flag = 0 then .l106560 else .l106565)
        next (resultStore mem sp out flag) ∧
      next[7] = ⟨64, out⟩ ∧ Preserved args next ∧
      (flag ≠ 0 → next[0] = ⟨64, 0⟩) := by
  dsimp only
  let staged := memCopy mem (sp + 72) (sp + 160) 88
  let flag := selectedByte tag affine identity
  let selected := memStore staged (sp + 160) flag
  have stack' : Writable code staged sp 249 := stack.memStore _ _
  have stageGuard : StoreOk code mem (sp + 72) 88 0x106501 3 :=
    ParseSignature.storeOk_of_codeRange (off := 13) (stack.of_offsets rfl (addr_self _) (by decide))
      (fun x hx => hcode x (code_l1064f4 x hx)) (by decide)
  have srcRead : Readable mem (sp + 160) 88 := stack.readable.of_offsets rfl (addr_self _) (by decide)
  have apartStage : (sp + 72).toNat + 88 ≤ (sp + 160).toNat := by
    rw [toNat_of_offsets (a := sp + 72) rfl (addr_self _) stack.readable.low (n := 88) (by decide),
      toNat_of_offsets (a := sp + 160) rfl (addr_self _) stack.readable.low (n := 88) (by decide)]
    change sp.toNat + 72 + 88 ≤ sp.toNat + 160
    omega
  have byteAfter (off : BitVec 64) (separate : RangeApart (sp + 72) 88 (sp + off) 1) :
      memLoad staged (sp + off) 8 = memLoad mem (sp + off) 8 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ separate
  obtain ⟨a, stageStep, tagA, tagC, keepA⟩ :=
    stage sp tag rsp src (copyGuard df srcRead stageGuard (.inr apartStage))
      (LoadOk.of_offsets stack'.readable rfl (addr_self _) (by decide))
      ((byteAfter 4 (RangeApart.of_offsets rfl rfl (by decide))).trans tagByte)
  have atSelect : ∃ b : Values Value Reg.count, Reaches code .l1064f4 args mem .l106518 b staged ∧
      b[0] = ⟨64, tag.setWidth 64⟩ ∧ Preserved args b := by
    by_cases inRange : 2 ≤ tag.toNat ∧ tag.toNat < 6
    · exact ⟨a, reaches_jump (by simpa only [inRange, and_self, ↓reduceIte] using stageStep), tagA, keepA⟩
    · have tz : tag = 0 := by
        rcases valid with e | rfl | rfl | rfl | rfl
        · exact e
        all_goals exact False.elim (inRange (by decide))
      obtain ⟨b, hz, al, keepB⟩ := zeroTag (args := a) (mem := staged) (code := code)
        (by rw [tagC, tz]; rfl)
      exact ⟨b, (reaches_jump (by simpa only [inRange, and_self, ↓reduceIte] using stageStep)).trans (reaches_jump hz),
        al.trans tagA, keepA.trans keepB⟩
  obtain ⟨b, reachB, al, keepB⟩ := atSelect
  have writeFlag : StoreOk code staged (sp + 160) 1 0x10652c 7 :=
    ParseSignature.storeOk_of_codeRange (off := 20) (stack'.of_offsets rfl (addr_self _) (by decide))
      (fun x hx => hcode x (code_l106518 x hx)) (by decide)
  have stack'' : Writable code selected sp 249 := stack'.memStore _ _
  obtain ⟨c, test, cdi, keepC⟩ :=
    select (args := b) (mem := staged) sp out tag affine identity
      ((congrArg (Value.get 64) (keepB.reg 4 (by decide))).trans rsp)
      ((congrArg (Value.get 64) (keepB.reg 15 (by decide))).trans dst)
      (by rw [al]; change (tag.setWidth 64).setWidth 8 = tag; simp)
      ((congrArg (fun v : Value => (v.get 64).setWidth 8) (keepB.reg 12 (by decide))).trans r12)
      (LoadOk.of_offsets stack'.readable rfl (addr_self _) (by decide))
      ((byteAfter 248 (RangeApart.of_offsets rfl rfl (by decide))).trans affineByte)
      writeFlag (LoadOk.of_offsets stack''.readable rfl (addr_self _) (by decide))
  have keep := keepB.trans keepC
  by_cases reject : flag = 0
  · have path := reachB.trans (reaches_jump (by simpa only [← show flag = selectedByte tag affine identity from rfl,
        reject, ↓reduceIte] using test))
    exact ⟨c, by simpa only [resultStore, ← show flag = selectedByte tag affine identity from rfl,
      reject, ↓reduceIte, selected, staged] using path, cdi, keep, fun h => (h reject).elim⟩
  · have pass : Reaches code .l1064f4 args mem .l106548 c selected := reachB.trans (reaches_jump (by
      simpa only [← show flag = selectedByte tag affine identity from rfl, reject, ↓reduceIte] using test))
    have out' : Writable code selected (out + 8) 88 :=
      (output.memStore _ _).memStore _ _
    have outGuard : StoreOk code selected (out + 8) 88 0x106556 3 :=
      ParseSignature.storeOk_of_codeRange (off := 14) out' (fun x hx => hcode x (code_l106548 x hx))
        (by decide)
    have rep : RepMovsOk code selected (c[22].get 1) (sp + 72) (out + 8) 11 8 0x106556 3 :=
      copyGuard ((congrArg (Value.get 1) (keep.reg 22 (by decide))).trans df)
        (stack''.readable.of_offsets (a := sp + 72) rfl (addr_self _) (by decide)) outGuard apart
    obtain ⟨d, write, eax, edi, keepD⟩ :=
      copyOutput (args := c) sp out ((congrArg (Value.get 64) (keep.reg 4 (by decide))).trans rsp)
        (congrArg (Value.get 64) cdi) ((congrArg (Value.get 64) (keep.reg 15 (by decide))).trans dst) rep
    refine ⟨d, ?_, edi, keep.trans keepD, fun _ => eax⟩
    simpa only [resultStore, ← show flag = selectedByte tag affine identity from rfl, reject,
      ↓reduceIte, selected, staged] using pass.trans (reaches_jump write)

theorem resultStore_frame (mem : Ram) (sp out : BitVec 64) (flag : BitVec 8)
    {regions : List Prelude.MemoryRegion} (stageSpace : InRegions regions (sp + 72) 88)
    (flagSpace : InRegions regions (sp + 160) 1)
    (outputSpace : flag ≠ 0 → InRegions regions (out + 8) 88) :
    RamWriteFrame mem (resultStore mem sp out flag) regions := by
  let staged := memCopy mem (sp + 72) (sp + 160) 88
  have hs : RamWriteFrame mem staged regions :=
    (RamWriteFrame.refl mem regions).memStore _ stageSpace
  have ht := hs.memStore flag flagSpace
  unfold resultStore
  split
  · exact ht
  · rename_i ok
    exact ht.memStore _ (outputSpace ok)

theorem resultStore_load {mem : Ram} {sp out : BitVec 64} {flag : BitVec 8}
    (accepted : flag ≠ 0) (off width : Nat) (inside : off + width / 8 ≤ 88) :
    memLoad (resultStore mem sp out flag) (out + 8 + BitVec.ofNat 64 off) width =
      memLoad mem (sp + 160 + BitVec.ofNat 64 off) width := by
  simpa only [resultStore, accepted, ↓reduceIte] using output_load inside mem sp out flag

theorem resultStore_affine {mem : Ram} {sp out : BitVec 64} {flag : BitVec 8}
    {x y : Fin Common.Field.modulus} {magnitude : Nat} (accepted : flag ≠ 0)
    (payload : AffineAt mem (sp + 160) x y magnitude) :
    AffineAt (resultStore mem sp out flag) (out + 8) x y magnitude :=
  payload.of_copy (resultStore_load accepted)

end K256.Proofs.Sec1.Parser.Result
