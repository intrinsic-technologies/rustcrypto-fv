import K256.Proofs.Sec1.Affine.Compressed.Emit.Stage
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR K256.Proofs.Common.Field K256.Proofs.Sec1.Serialize.Coordinates

private theorem stageGuard {m : Ram} {code : CodeMap} {sp off pc : Word} {n len : Nat}
    (h : Writable code m (sp - 8) 448) (b : (off - (0 - 8)).toNat + n ≤ 448)
    (hc : ∀ e ∈ codeRange 0x120e9b bytes_l120e9b, e ∈ code)
    (hp : (pc - 0x120e9b).toNat + len ≤ bytes_l120e9b.length) :
    StoreOk code m (sp + off) n pc len := by
  have e := ParseSignature.storeOk_of_codeRange (h.of_offsets (a := sp+off) rfl (addr_sub sp 8) b) hc hp
  have ep : 0x120e9b + BitVec.ofNat 64 (pc-0x120e9b).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [ep] at e

private theorem stageLoad {m : Ram} {sp off : Word} {n : Nat}
    (h : Readable m (sp - 8) 448) (b : (off - (0 - 8)).toNat + n ≤ 448) :
    LoadOk m (sp + off) n := LoadOk.of_offsets h rfl (addr_sub sp 8) b

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem outputCall (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : Word) (rsp : args[4].get 64 = sp) (df : args[22].get 1 = 0)
    (hdst : memLoad mem (sp+136) 64 = dst) (stack : Writable code mem (sp-8) 448)
    (hw : Writable code mem dst 89)
    (apart : dst.toNat + 89 ≤ (sp-8).toNat ∨ (sp-8).toNat + 448 ≤ dst.toNat)
    (cover : ∀ e ∈ codeRange 0x120e9b bytes_l120e9b, e ∈ code) :
    let st := stagePoint mem sp (savedX mem sp)
    let copied := memCopy st dst (sp+352) 88
    ∃ next, program.runBlock (dialect code) ⟨.l120e9b, args, mem⟩ =
      .call ⟨.l127d50, next, memStore copied (sp-8) (0x120f13 : Word)⟩ (callFrame .l120f13 0x120f13) ∧
      next[4] = ⟨64, sp-8⟩ ∧ next[3] = ⟨64, dst⟩ ∧
      next[7].get 64 = (((memLoad mem (sp+128) 64).setWidth 8 &&& memLoad mem (sp+32) 8).setWidth 64) ∧
      next[22] = args[22] ∧ next[39] = args[39] ∧ next[50] = args[50] ∧ next[51] = args[51] := by
  let st := stagePoint mem sp (savedX mem sp)
  let cp := memCopy st dst (sp+352) 88
  have sw : Writable code st (sp-8) 448 := by
    dsimp only [st, stagePoint]
    repeat' apply Writable.memStore
    exact stack
  have dw : Writable code st dst 89 := by
    dsimp only [st, stagePoint]
    repeat' apply Writable.memStore
    exact hw
  have rep : RepMovsOk code st (args[22].get 1) (sp+352) dst 11 8 0x120efc 3 := by
    have r : Readable st (sp+352) 88 := sw.readable.of_offsets rfl (addr_sub sp 8) (by decide)
    have d : StoreOk code st dst 88 0x120efc 3 :=
      ParseSignature.storeOk_of_codeRange (off := 97) (dw.sub (Nat.le_refl _) (by omega)) cover (by decide)
    have sn := toNat_of_offsets (a := sp + 352) rfl (addr_sub sp 8) stack.readable.low (n := 88) (by decide)
    refine ⟨df, r.low, d.low, r.present, d.present, ?_, d.tables, d.apart, d.notCode⟩
    change (sp+352).toNat + 88 ≤ dst.toNat ∨ dst.toNat + 88 ≤ (sp+352).toNat
    change (sp+352).toNat = (sp-8).toNat + 360 at sn
    omega
  have readCp (k : Word) (n : Nat) (bound : (k - (0 - 8)).toNat + n/8 ≤ 448) :
      memLoad cp (sp+k) n = memLoad st (sp+k) n := by
    apply memLoad_memStore_of_rangeApart
    have hs := toNat_of_offsets (a := sp+k) rfl (addr_sub sp 8) stack.readable.low bound
    have hl := stack.readable.low
    have hd := hw.readable.low
    apply RangeApart.of_toNat <;> omega
  have rc128 := readCp 128 64 (by decide)
  have rc32 := readCp 32 8 (by decide)
  dsimp only
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval [rsp]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | refine stageGuard (sp := sp) ?_ (by decide) cover (by decide +kernel)
          repeat' apply Writable.memStore
          exact stack
        | apply stageLoad (sp := sp) _ (by decide)
          repeat' apply Readable.memStore
          exact stack.readable)
    simp (disch := decide +kernel) only [skipStore, hdst]
    refine Eq.trans (ite_eq_left (Or.inr ?_)) ?_
    exact rep
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | rw [addr_sub sp 8]
          refine stageGuard (sp := sp) ?_ (by decide) cover (by decide +kernel)
          unfold memCopy
          repeat' apply Writable.memStore
          exact stack
        | apply stageLoad (sp := sp) _ (by decide)
          unfold memCopy
          repeat' apply Readable.memStore
          exact stack.readable)
    rfl
  case post =>
    refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
    change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
    rw [setWidth_mergeGPR8]
    change ((memLoad cp (sp+128) 64).setWidth 8 &&& memLoad cp (sp+32) 8).setWidth 64 = _
    rw [rc128, rc32]
    simp (disch := decide +kernel) only [st, stagePoint, skipStore]

end K256.Proofs.Sec1.Affine.Compressed
