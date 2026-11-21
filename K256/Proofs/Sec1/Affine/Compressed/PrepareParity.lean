import K256.Proofs.Sec1.Affine.Compressed.Parity
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

open K256.Proofs.Common.Field

open Serialize.Coordinates

def negationStack (mem : Ram) (sp : Word) (a : Limbs) : Ram :=
  let n := negated a
  let m := memStore mem (sp + 96) n[0]
  let m := memStore m (sp + 40) n[1]
  let m := memStore m (sp + 8) n[2]
  let m := memStore m (sp + 16) n[4]
  memStore m (sp - 8) (0x120dff : Word)

private theorem spillGuard {m : Ram} {code : CodeMap} {sp off pc : Word} {len : Nat}
    (h : Writable code m (sp - 8) 272)
    (b : (off - (0 - 8)).toNat + 8 ≤ 272)
    (hc : ∀ e ∈ codeRange 0x120d83 bytes_l120d83, e ∈ code)
    (hp : (pc - 0x120d83).toNat + len ≤ bytes_l120d83.length) :
    StoreOk code m (sp + off) 8 pc len := by
  have e := ParseSignature.storeOk_of_codeRange (h.of_offsets (a := sp+off) rfl (addr_sub sp 8) b) hc hp
  have ep : 0x120d83 + BitVec.ofNat 64 (pc-0x120d83).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [ep] at e

private theorem rootLoad {m : Ram} {sp off : Word}
    (h : Readable m (sp - 8) 272) (b : (off - (0 - 8)).toNat + 8 ≤ 272) :
    LoadOk m (sp + off) 8 := LoadOk.of_offsets h rfl (addr_sub sp 8) b

theorem prepareParity (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : Word) (a : Limbs) (rsp : args[4].get 64 = sp) (hw : Writable code mem (sp-8) 272)
    (ha : WordsAt mem (sp + 224) 64 a) (cover : ∀ e ∈ codeRange 0x120d83 bytes_l120d83, e ∈ code) :
    ∃ next, program.runBlock (dialect code) ⟨.l120d83, args, mem⟩ =
      .call ⟨.l127d50, next, negationStack mem sp a⟩ (callFrame .l120dff 0x120dff) ∧
      next[4] = ⟨64, sp - 8⟩ ∧ next[7].get 64 = ((a[0].setWidth 8 &&& 1).setWidth 64) ∧
      next[14] = ⟨64,a[0]⟩ ∧ next[15] = ⟨64,a[1]⟩ ∧ next[12] = ⟨64,a[2]⟩ ∧
      next[13] = ⟨64,a[3]⟩ ∧ next[5] = ⟨64,a[4]⟩ ∧ next[3] = ⟨64,(negated a)[3]⟩ ∧
      next[22] = args[22] ∧ next[39] = args[39] ∧ next[50] = args[50] ∧ next[51] = args[51] := by
  have outside (m : Ram) (o k v : Word) (b : 8 ≤ (k-o).toNat ∧ 8 ≤ (o-k).toNat) :
      memLoad (memStore m (sp+o) v) (sp+k) 64 = memLoad m (sp+k) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl b)
  have v0 : memLoad mem (sp + 224) 64 = a[0] := by
    have h := ha 0 (by decide)
    rw [wordAddr, BitVec.add_assoc] at h
    exact h
  have v1 : memLoad mem (sp + 232) 64 = a[1] := by
    have h := ha 1 (by decide)
    rw [wordAddr, BitVec.add_assoc] at h
    exact h
  have v2 : memLoad mem (sp + 240) 64 = a[2] := by
    have h := ha 2 (by decide)
    rw [wordAddr, BitVec.add_assoc] at h
    exact h
  have v3 : memLoad mem (sp + 248) 64 = a[3] := by
    have h := ha 3 (by decide)
    rw [wordAddr, BitVec.add_assoc] at h
    exact h
  have v4 : memLoad mem (sp + 256) 64 = a[4] := by
    have h := ha 4 (by decide)
    rw [wordAddr, BitVec.add_assoc] at h
    exact h
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval [rsp]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | refine spillGuard (sp := sp) ?_ (by decide) cover (by decide +kernel)
          repeat' apply Writable.memStore
          exact hw
        | rw [addr_sub sp 8]
          refine spillGuard (sp := sp) ?_ (by decide) cover (by decide +kernel)
          repeat' apply Writable.memStore
          exact hw
        | apply rootLoad (sp := sp) _ (by decide)
          repeat' apply Readable.memStore
          exact hw.readable)
    simp (disch := decide +kernel) only [outside,v0,v1,v2,v3,v4]
    simp only [negationStack, negated, Vector.getElem_ofFn]
    rfl
  case post =>
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
    · change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
      simp [setWidth_mergeGPR8]
    · simp only [negated, Vector.getElem_ofFn]
      rfl

end K256.Proofs.Sec1.Affine.Compressed
