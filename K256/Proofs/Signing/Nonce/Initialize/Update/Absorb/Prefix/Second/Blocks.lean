import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Words
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {a : Verify.Core.Registers} {m : Ram} {s src dst stop : BitVec 64}

def branchRegisters (a : Verify.Core.Registers) (s : BitVec 64) :=
  (((a.set 5 ⟨64,s+456⟩).set 3 ⟨64,0⟩).set 16 ⟨1,1⟩).set 19 ⟨1,0⟩

local macro "prefix_regs" : tactic =>
  `(tactic| (congr 2
             apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
               fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
             intro i
             finite_cases i <;> (try simp only [Vector.getElem_set]) <;> rfl))

theorem secondBranch (rsp : a[4].get 64 = s) (rd : LoadOk m (s+455) 1)
    (used : memLoad m (s+455) 8 = 0) :
    program.runBlock (dialect Extracted.programImage) ⟨.l104579,a,m⟩ =
      .jump ⟨.l104593,branchRegisters a s,m⟩ := by
  have cf : (cmpSpec (0 : BitVec 64) 31).CF = true := by decide
  have zf : (cmpSpec (0 : BitVec 64) 31).ZF = false := by decide
  unfold branchRegisters
  cfg_eval [rsp, rd, used, cf, zf]
  simp only [Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  prefix_regs

def copiedRegisters (a : Verify.Core.Registers) (m : Ram) (src stop : BitVec 64) :=
  ((((a.set 0 ⟨64,32⟩).set 1 ⟨64,memLoad m (src+8) 64⟩).set 3 ⟨64,32⟩).set 15 ⟨64,stop⟩).set 19 ⟨1,0⟩

def copiedMemory (m : Ram) (s dst src : BitVec 64) :=
  memStore (UpdateV.Append.stored m dst src) (s+455) (32 : BitVec 8)

set_option maxHeartbeats 1200000 in
theorem secondCopy (rsp : a[4].get 64 = s) (zero : a[3].get 64 = 0)
    (buffer : a[13].get 64 = dst) (rd : LoadOk m (s+112) 8)
    (source : memLoad m (s+112) 64 = src) (access : WordAccess m src dst (s+455))
    (stopRd : LoadOk (copiedMemory m s dst src) (s+8) 8)
    (stopEq : memLoad (copiedMemory m s dst src) (s+8) 64 = stop) :
    program.runBlock (dialect Extracted.programImage) ⟨.l104593,a,m⟩ =
      .jump ⟨.l1045d5,copiedRegisters a m src stop,copiedMemory m s dst src⟩ := by
  subst stop
  obtain ⟨r1,w1,r2,e2,w2,r3,r4,e3,e4,w3,w4,w5⟩ := access
  have code := fun x hx => Common.fnCode_subset_programImage x (code_l104593 x hx)
  have g1 := ParseSignature.storeOk_of_codeRange (off := 9) (len := 5) w1 code (by decide)
  have g2 := ParseSignature.storeOk_of_codeRange (off := 18) (len := 5) w2 code (by decide)
  have g3 := ParseSignature.storeOk_of_codeRange (off := 30) (len := 5) w3 code (by decide)
  have g4 := ParseSignature.storeOk_of_codeRange (off := 35) (len := 5) w4 code (by decide)
  have g5 := ParseSignature.storeOk_of_codeRange (off := 43) (len := 7) w5 code (by decide)
  have merged : mergeGPR 8 32 0 = 32 := by decide
  unfold copiedMemory UpdateV.Append.stored at stopRd ⊢
  unfold UpdateV.Append.stored at g5
  unfold copiedRegisters
  cfg_eval [rsp, zero, buffer, rd, source, r1, r2, r3, r4, e2, e3, e4, g1, g2, g3, g4, g5, stopRd]
  simp only [merged, BitVec.reduceSetWidth, e3, e4, r3, r4, ↓reduceIte]
  split <;> try (rename_i bad; exact (bad g1).elim)
  split <;> try (rename_i bad; exact (bad g2).elim)
  split <;> try (rename_i bad; exact (bad g3).elim)
  split <;> try (rename_i bad; exact (bad g4).elim)
  split <;> try (rename_i bad; exact (bad g5).elim)
  split <;> try (rename_i bad; exact (bad stopRd).elim)
  split <;> try (rename_i h; exact False.elim ((by decide : (cmpSpec (32 : BitVec 8) 63).ZF ≠ true) h))
  prefix_regs

theorem secondTag (rsp : a[4].get 64 = s) (index : a[0].get 64 = 32)
    (guard : StoreOk Extracted.programImage m (s+424) 1 0x1045d5 8) :
    program.runBlock (dialect Extracted.programImage) ⟨.l1045d5,a,m⟩ =
      .jump ⟨.l1047c4,a.set 0 ⟨64,33⟩,memStore m (s+424) (1 : BitVec 8)⟩ := by
  cfg_eval [rsp, index, guard]
  prefix_regs

theorem secondUsed (rsp : a[4].get 64 = s) (index : a[0].get 64 = 33)
    (guard : StoreOk Extracted.programImage m (s+455) 1 0x1047c4 7) :
    program.runBlock (dialect Extracted.programImage) ⟨.l1047c4,a,m⟩ =
      .jump ⟨.l1047fb,a,memStore m (s+455) (33 : BitVec 8)⟩ := by
  cfg_eval [rsp, index, guard]
  prefix_regs

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix
