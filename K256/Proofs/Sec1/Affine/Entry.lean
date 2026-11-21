import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.ParseSignature.BlackBox

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

def saveRegisters (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[12].get 64)
  let mem := memStore mem (sp - 40) (args[3].get 64)
  mem

private theorem tagCarry : ∀ t : BitVec 8,
    (cmpSpec ((t.setWidth 64 - 2).setWidth 32) 4).CF = decide (2 ≤ t.toNat ∧ t.toNat < 6) := by
  decide +kernel

theorem affineEntry {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp src dst : BitVec 64)
    (rsp : args[4].get 64 = sp) (rsi : args[6].get 64 = src) (rdi : args[7].get 64 = dst)
    (stack : Writable code mem (sp - 40) 40) (room : 40 ≤ sp.toNat)
    (readTag : Readable mem src 1) (apart : Outside [⟨(sp - 40).toNat, 40⟩] src 1) :
    let tag := memLoad mem src 8
    let coordinates := decide (2 ≤ tag.toNat ∧ tag.toNat < 6)
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l121480, args, mem⟩ =
        (if coordinates then .jump ⟨.l1214a0, next, saveRegisters args mem⟩
         else .jump ⟨.l1214d0, next, saveRegisters args mem⟩) ∧
      next[0] = ⟨64, tag.zeroExtend 64⟩ ∧ next[1] = ⟨64, tag.zeroExtend 64⟩ ∧
      next[2] = ⟨64, src⟩ ∧ next[3] = ⟨64, dst⟩ ∧ next[4] = ⟨64, sp - 136⟩ ∧
      RamWriteFrame mem (saveRegisters args mem) [⟨(sp - 40).toNat, 40⟩] ∧
      ∀ i : Fin Reg.count, i.val ∉ [0, 1, 2, 3, 4, 6, 16] → next[i] = args[i] := by
  let saved := [MemoryRegion.mk (sp - 40).toNat 40]
  have addr (k : Nat) (hk : k ≤ 40) : (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
    have index : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, index]; omega), index]
  have addr40 : (sp - 40).toNat = sp.toNat - 40 := addr 40 (by decide)
  have makeGuard {m : Ram} (h : RamWriteFrame mem m saved) (k : Nat)
      (hk : k ≤ 40) (hk' : 8 ≤ k) {off len : Nat} (hit : off + len ≤ bytes_l121480.length) :
      StoreOk code m (sp - BitVec.ofNat 64 k) 8 (0x121480 + BitVec.ofNat 64 off) len := by
    apply ParseSignature.storeOk_of_codeRange _ (fun x hx => hcode x (code_l121480 x hx)) hit
    have w := stack.of_frame h
    apply w.sub
    all_goals rw [addr k hk, addr40] <;> omega
  have push {m : Ram} (h : RamWriteFrame mem m saved) (k : Nat) (v : BitVec 64)
      (hk : k ≤ 40) (hk' : 8 ≤ k) : RamWriteFrame mem (memStore m (sp - BitVec.ofNat 64 k) v) saved := by
    apply h.memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp - 40).toNat ≤ _ ∧ (sp - BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 40).toNat + 40 ∧
      (sp - BitVec.ofNat 64 k).toNat + 8 ≤ 2^64
    rw [addr k hk, addr40]
    have := sp.isLt
    omega
  let m0 := mem
  have f0 : RamWriteFrame mem m0 saved := .refl _ _
  have g1 : StoreOk code m0 (sp - 8) 8 0x121480 1 :=
    makeGuard (off := 0) f0 8 (by decide) (by decide) (by decide)
  let m1 := memStore m0 (sp - 8) (args[5].get 64)
  have f1 : RamWriteFrame mem m1 saved := push f0 8 _ (by decide) (by decide)
  have g2 : StoreOk code m1 (sp - 16) 8 0x121481 2 :=
    makeGuard (off := 1) f1 16 (by decide) (by decide) (by decide)
  let m2 := memStore m1 (sp - 16) (args[15].get 64)
  have f2 : RamWriteFrame mem m2 saved := push f1 16 _ (by decide) (by decide)
  have g3 : StoreOk code m2 (sp - 24) 8 0x121483 2 :=
    makeGuard (off := 3) f2 24 (by decide) (by decide) (by decide)
  let m3 := memStore m2 (sp - 24) (args[14].get 64)
  have f3 : RamWriteFrame mem m3 saved := push f2 24 _ (by decide) (by decide)
  have g4 : StoreOk code m3 (sp - 32) 8 0x121485 2 :=
    makeGuard (off := 5) f3 32 (by decide) (by decide) (by decide)
  let m4 := memStore m3 (sp - 32) (args[12].get 64)
  have f4 : RamWriteFrame mem m4 saved := push f3 32 _ (by decide) (by decide)
  have g5 : StoreOk code m4 (sp - 40) 8 0x121487 1 :=
    makeGuard (off := 7) f4 40 (by decide) (by decide) (by decide)
  let m5 := memStore m4 (sp - 40) (args[3].get 64)
  have f5 : RamWriteFrame mem m5 saved := push f4 40 _ (by decide) (by decide)
  have load : LoadOk m5 src 1 :=
    let h := readTag.of_frame f5
    ⟨h.low, h.present⟩
  have tagSaved : memLoad m5 src 8 = memLoad mem src 8 := f5.memLoad_eq apart
  dsimp only
  let tag := memLoad mem src 8
  let coordinates := decide (2 ≤ tag.toNat ∧ tag.toNat < 6)
  let delta := ((tag.setWidth 64 - 2).setWidth 32).setWidth 64
  let next := (((((((args.set 0 ⟨64, tag.setWidth 64⟩).set 1 ⟨64, tag.setWidth 64⟩).set 2
    ⟨64, src⟩).set 3 ⟨64, dst⟩).set 4 ⟨64, sp - 136⟩).set 6 ⟨64, delta⟩).set 16 (.ofBool coordinates))
  refine ⟨next, ?exec, ?rest⟩
  case exec =>
    cfg_eval
    dsimp only [m5, m4, m3, m2, m1, m0] at g1 g2 g3 g4 g5 tagSaved load
    simp only [rsp, rsi, rdi, g1, g2, g3, g4, g5, load, tagSaved, ↓reduceIte]
    simp only [saveRegisters, rsp, tagCarry, Bool.not_eq_true']
    dsimp only [next, tag, coordinates, delta]
    by_cases h : 2 ≤ (memLoad mem src 8).toNat ∧ (memLoad mem src 8).toNat < 6
    all_goals simp only [h, and_self, decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    all_goals congr 2 <;>
      apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b
        from fun h => Vector.ext fun i hi => h ⟨i, hi⟩) <;> intro i <;>
      simp only [Vector.getElem_set] <;> finite_cases i <;> rfl
  case rest =>
    have savedFrame : RamWriteFrame mem (saveRegisters args mem) saved := by
      simpa only [saveRegisters, rsp] using f5
    refine ⟨?_, ?_, ?_, ?_, ?_, savedFrame, ?_⟩ <;> try (simp only [next, Vector.getElem_set]; rfl)
    intro i
    change Fin 53 at i
    intro hi
    change next[i.val] = args[i.val]
    simp only [next, Vector.getElem_set]
    finite_cases i <;> intro h <;> first | rfl | exact (h (by decide)).elim

end K256.Proofs.Sec1.Affine
