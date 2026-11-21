import K256.Proofs.Signing.UpdateV.Prepare.Append.Blocks
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.First

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {a : Vector Value Reg.count} {m : Ram} {sp src key slices : BitVec 64} {code : CodeMap}

local macro "first_regs" : tactic =>
  `(tactic| (congr 2
             apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
               fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
             intro i
             finite_cases i <;> (try simp only [Vector.getElem_set]) <;> rfl))

def initialArgs (a : Vector Value Reg.count) (sp src : BitVec 64) :=
  (((((a.set 3 ⟨64, 0⟩).set 6 ⟨64, src⟩).set 13 ⟨64, sp+224⟩).set 16 ⟨1, 1⟩).set 19 ⟨1, 0⟩)

theorem initial (rsp : a[4].get 64 = sp) (bp : a[5].get 64 = key)
    (rd : LoadOk m (sp+287) 1) (used : memLoad m (sp+287) 8 = 0)
    (wr : StoreOk code m (sp+112) 8 0x104185 5) :
    program.runBlock (dialect code) ⟨.l10416d,a,m⟩ =
      .jump ⟨.l104190,initialArgs a sp (key+32),memStore m (sp+112) (key+32)⟩ := by
  unfold initialArgs
  have cf : (cmpSpec (0 : BitVec 64) 31).CF = true := by decide
  have zf : (cmpSpec (0 : BitVec 64) 31).ZF = false := by decide
  cfg_eval [rsp, bp, rd, used, wr, cf, zf]
  simp only [Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  first_regs

def copiedArgs (a : Vector Value Reg.count) (m : Ram) (src : BitVec 64) :=
  (((a.set 0 ⟨64,32⟩).set 1 ⟨64, memLoad m (src+8) 64⟩).set 3 ⟨64,32⟩).set 19 ⟨1,0⟩

theorem copy (rsp : a[4].get 64 = sp) (si : a[6].get 64 = src)
    (buf : a[13].get 64 = sp+224) (zero : a[3].get 64 = 0) :
    let dst := sp+224
    let m₁ := memStore m (dst+24) (memLoad m (src+24) 64)
    let m₂ := memStore m₁ (dst+16) (memLoad m (src+16) 64)
    let m₃ := memStore m₂ (dst+8) (memLoad m (src+8) 64)
    LoadOk m (src+24) 8 → StoreOk code m (dst+24) 8 0x104194 5 →
    LoadOk m₁ (src+16) 8 → memLoad m₁ (src+16) 64 = memLoad m (src+16) 64 →
    StoreOk code m₁ (dst+16) 8 0x10419d 5 →
    LoadOk m₂ src 8 → LoadOk m₂ (src+8) 8 →
    memLoad m₂ src 64 = memLoad m src 64 →
    memLoad m₂ (src+8) 64 = memLoad m (src+8) 64 →
    StoreOk code m₂ (dst+8) 8 0x1041a9 5 →
    StoreOk code m₃ dst 8 0x1041ae 5 →
    StoreOk code (UpdateV.Append.stored m dst src) (sp+287) 1 0x1041b6 7 →
    program.runBlock (dialect code) ⟨.l104190,a,m⟩ =
      .jump ⟨.l1041c8,copiedArgs a m src,
        memStore (UpdateV.Append.stored m dst src) (sp+287) (32 : BitVec 8)⟩ := by
  dsimp only
  intro rd₁ wr₁ rd₂ eq₂ wr₂ rd₃ rd₄ eq₃ eq₄ wr₃ wr₄ used
  unfold UpdateV.Append.stored at used ⊢
  simp only [show sp+224+24 = sp+248 by bv_omega, show sp+224+16 = sp+240 by bv_omega,
    show sp+224+8 = sp+232 by bv_omega] at wr₁ rd₂ eq₂ wr₂ rd₃ rd₄ eq₃ eq₄ wr₃ wr₄ used ⊢
  unfold copiedArgs
  have zf : (cmpSpec (32 : BitVec 8) 63).ZF = false := by decide
  cfg_eval [rsp, si, buf, zero, rd₁, wr₁, rd₂, eq₂, wr₂, rd₃, rd₄, eq₃, eq₄, wr₃, wr₄, used, zf]
  simp only [rd₃, rd₄, eq₃, eq₄, wr₃, wr₄, used, ↓reduceIte]
  simp only [show (cmpSpec (BitVec.setWidth 8 (mergeGPR 8 32 0)) 63).ZF = false by decide, Bool.false_eq_true, ↓reduceIte]
  first_regs

def taggedArgs (a : Vector Value Reg.count) (seed : Bool) :=
  (a.set 3 ⟨64,33⟩).set 19 (Value.ofBool (!seed))

theorem mark (seed : Bool) (rsp : a[4].get 64 = sp) (idx : a[0].get 64 = 32)
    (count : a[15].get 64 = if seed then 3 else 0)
    (wr : StoreOk code m (sp+256) 1 0x1041c8 8)
    (used : StoreOk code (memStore m (sp+256) (0 : BitVec 8)) (sp+287) 1 0x1041d3 7) :
    program.runBlock (dialect code) ⟨.l1041c8,a,m⟩ =
      .jump ⟨if seed then .l1041e3 else .l1046a2,taggedArgs a seed,
        memStore (memStore m (sp+256) (0 : BitVec 8)) (sp+287) (33 : BitVec 8)⟩ := by
  have addr : sp+32+224 = sp+256 := by bv_omega
  cases seed <;> unfold taggedArgs <;> cfg_eval [rsp, idx, count, addr, wr, used, testFlags]
  all_goals simp only [beq_self_eq_true, show ((3 : BitVec 64) == 0) = false by decide,
    Bool.false_eq_true, ↓reduceIte]
  all_goals first_regs

def seededArgs (a : Vector Value Reg.count) (slices : BitVec 64) := a.set 15 ⟨64,slices⟩

theorem beginLoop (rsp : a[4].get 64 = sp) (bp : a[5].get 64 = key)
    (base : a[14].get 64 = slices) (count : a[15].get 64 = 3)
    (wr : StoreOk code m (sp+120) 8 0x1041e3 5)
    (stop : StoreOk code (memStore m (sp+120) key) (sp+8) 8 0x1041ef 5) :
    program.runBlock (dialect code) ⟨.l1041e3,a,m⟩ =
      .jump ⟨.l10422b,seededArgs a slices,
        memStore (memStore m (sp+120) key) (sp+8) (slices+48)⟩ := by
  unfold seededArgs
  cfg_eval [rsp, bp, base, count, wr, stop, BitVec.add_comm (48 : BitVec 64) slices]
  first_regs

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.First
