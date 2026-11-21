import K256.Proofs.Verify.LIR.Fn104970
import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.Choice
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Signing.UpdateV.Append

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {a : Vector Value Reg.count} {m : Ram} {sp src dst : BitVec 64} {code : CodeMap}

def branchArgs (a : Vector Value Reg.count) (src : BitVec 64) : Vector Value Reg.count :=
  (((a.set 3 ⟨64, src+32⟩).set 15 ⟨64, 0⟩).set 16 ⟨1, 1⟩).set 19 ⟨1, 0⟩

local macro "append_regs" : tactic =>
  `(tactic| (congr 2
             apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
               fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
             intro i
             finite_cases i <;> (try simp only [Vector.getElem_set]) <;> rfl))

theorem branch (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = src)
    (rd : LoadOk m (sp + 231) 1) (used : memLoad m (sp + 231) 8 = 0) :
    program.runBlock (dialect code) ⟨.l104b63, a, m⟩ =
      .jump ⟨.l104b76, branchArgs a src, m⟩ := by
  unfold branchArgs
  have cf : (cmpSpec (0 : BitVec 64) 31).CF = true := by decide
  have zf : (cmpSpec (0 : BitVec 64) 31).ZF = false := by decide
  cfg_eval [rsp, rbx, rd, used, cf, zf]
  simp only [Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  append_regs

def stored (m : Ram) (dst src : BitVec 64) : Ram :=
  let m₁ := memStore m (dst + 24) (memLoad m (src + 24) 64)
  let m₂ := memStore m₁ (dst + 16) (memLoad m (src + 16) 64)
  let m₃ := memStore m₂ (dst + 8) (memLoad m (src + 8) 64)
  memStore m₃ dst (memLoad m src 64)

def valueArgs (a : Vector Value Reg.count) (m : Ram) (src : BitVec 64) : Vector Value Reg.count :=
  ((a.set 0 ⟨64, memLoad m src 64⟩).set 1 ⟨64,memLoad m (src+8) 64⟩).set 15 ⟨64,32⟩

theorem valueStores (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = src)
    (r14 : a[14].get 64 = dst) (r15 : a[15].get 64 = 0) :
    let m₁ := memStore m (dst + 24) (memLoad m (src + 24) 64)
    let m₂ := memStore m₁ (dst + 16) (memLoad m (src + 16) 64)
    let m₃ := memStore m₂ (dst + 8) (memLoad m (src + 8) 64)
    LoadOk m (src+24) 8 → StoreOk code m (dst+24) 8 0x104b7a 5 →
    LoadOk m₁ (src+16) 8 → memLoad m₁ (src+16) 64 = memLoad m (src+16) 64 →
    StoreOk code m₁ (dst+16) 8 0x104b83 5 →
    LoadOk m₂ src 8 → LoadOk m₂ (src+8) 8 →
    memLoad m₂ src 64 = memLoad m src 64 →
    memLoad m₂ (src+8) 64 = memLoad m (src+8) 64 →
    StoreOk code m₂ (dst+8) 8 0x104b8f 5 →
    StoreOk code m₃ dst 8 0x104b94 4 → StoreOk code (stored m dst src) (sp+231) 1 0x104b9c 8 →
    program.runBlock (dialect code) ⟨.l104b76,a,m⟩ =
      .jump ⟨.l104c06,valueArgs a m src,memStore (stored m dst src) (sp+231) (32 : BitVec 8)⟩ := by
  dsimp only
  intro rd₁ wr₁ rd₂ eq₂ wr₂ rd₃ rd₄ eq₃ eq₄ wr₃ wr₄ used
  unfold stored at used ⊢
  unfold valueArgs
  cfg_eval [rsp, rbx, r14, r15, rd₁, wr₁, rd₂, eq₂, wr₂, rd₃, rd₄, eq₃, eq₄, wr₃, wr₄, used]
  simp only [rd₃, rd₄, eq₃, eq₄, wr₃, wr₄, used, ↓reduceIte]
  append_regs

def copyArgs (a : Vector Value Reg.count) (sp : BitVec 64) : Vector Value Reg.count :=
  ((((a.set 2 ⟨64,168⟩).set 4 ⟨64,sp-8⟩).set 6 ⟨64,sp+104⟩).set 7 ⟨64,sp+272⟩).set 14 ⟨64,sp+272⟩

theorem copyCall (rsp : a[4].get 64 = sp) (push : StoreOk code m (sp-8) 8 0x104c1b 6)
    (read : LoadOk m 0x203dd0 8) (got : memLoad m 0x203dd0 64 = 0x12a820) :
    program.runBlock (dialect code) ⟨.l104c06,a,m⟩ =
      .call ⟨.l12a820,copyArgs a sp,memStore m (sp-8) (0x104c21 : BitVec 64)⟩
        (K256.Proofs.Verify.Hash.Update.returnFrame .l104c21 0x104c21) := by
  unfold copyArgs
  cfg_eval [rsp, push, read, got]
  append_regs

end K256.Proofs.Signing.UpdateV.Append
