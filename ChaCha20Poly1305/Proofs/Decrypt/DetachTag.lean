import ChaCha20Poly1305.Proofs.Decrypt.KeyCall
import ChaCha20Poly1305.Proofs.Decrypt.TagCompare

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash

@[refine_layout] def basic (fr : Activation) : List Atom :=
  [.gpr 4 fr.rsp,.reg 22 ⟨1,0⟩,.reg 39 ⟨32,fr.mxcsr⟩,.reg 50 ⟨16,fr.ftw⟩,.reg 51 ⟨16,fr.fcw⟩]

@[refine_layout] def checkTag (fr : Activation) (x : TagCompare.Input) (good : Bool) : Micro.Step where
  entry := .l100577
  exit := if good then .l1005d2 else .l1005ea
  pre := regs fr ++ [.gpr 5 x.suppliedHi,.mem (fr.rsp+160) 64 x.computedLo,.mem (fr.rsp+168) 64 x.computedHi,
    .mem (fr.rsp+200) 64 x.suppliedLo,.writable fr.rsp 208,
    .fact (fr.rsp.toNat+208≤0x100577 ∨ 0x1005d2≤fr.rsp.toNat)]
  post := if good then regs fr ++ [.gpr 5 x.suppliedHi] else basic fr ++ [.low 0 8 1]
  writes := [slot fr.rsp 6 1]

set_option maxHeartbeats 950000
set_option maxRecDepth 8000
set_option pp.maxSteps 130

theorem checkValid (fr : Activation) (x : TagCompare.Input) (good : Bool) (hg : TagCompare.ok x ↔ good=true) :
    Micro.Valid (checkTag fr x good) := by
  cases good <;> simp [TagCompare.ok] at hg
  all_goals unfold Micro.Valid
  all_goals refine_one [Micro.program,checkTag,setWidth_mergeGPR8]
  all_goals try assumption
  all_goals by_cases hlo : x.computedLo = x.suppliedLo <;> by_cases hhi : x.computedHi = x.suppliedHi
  all_goals try solve | exact False.elim (hg hlo hhi) | exact False.elim (hlo hg.1) | exact False.elim (hhi hg.2)
  all_goals simp only [TagCompare.flag] at hc
  all_goals simp +decide [hlo,hhi,TagCompare.lowMerge,BitVec.setWidth_setWidth_of_le] at hc

@[refine_layout] def msgFrame (fr : Activation) (vec : BitVec 64) :=
  {push fr with rsi:=vec,rdi:=fr.rsp+208}

@[refine_layout] def msgCall (x : Stream.Input) (raw : Raw) (src dst : BitVec (8*x.n.toNat)) (sp vec : BitVec 64) : Invoke.Edge where
  site := .l1005d2
  resume := .l1005e4
  callee := view x raw 1 [.mem x.buf (8*x.n.toNat) src] dst
  before fr := regs fr ++ [.gpr 5 fr.rbp] ++ space fr 424 ++ [.fact (fr.rsp=sp),.readable (fr.rsp+16) 8,
    .mem (fr.rsp+16) 64 vec] ++ (view x raw 1 [.mem x.buf (8*x.n.toNat) src] dst).pre (msgFrame fr vec)
  after fr := basic fr ++ [.gpr 0 0,.mem x.buf (8*x.n.toNat) dst]
  footprint := [⟨(sp+208).toNat+48,4⟩,⟨(sp+208).toNat+64,64⟩,⟨x.buf.toNat,x.n.toNat⟩]

attribute [local irreducible] memLoad memStore

set_option maxHeartbeats 2400000 in
theorem msgValid (x : Stream.Input) (raw : Raw) (src dst : BitVec (8*x.n.toNat)) (sp vec : BitVec 64) :
    (Invoke.layout (msgCall x raw src dst sp vec)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp
  refine_uir [Invoke.program]
  refine_lifted []
  prepare_call (fun m => ({fr with original:=m,rsp:=fr.rsp-8,ret:=0x1005e4,rdi:=fr.rsp+208,rsi:=vec,r12:=fr.rdi},()))
  · refine_close []
    all_goals simp only [BitVec.add_assoc] at atom36 atom37 atom38 atom39 atom40 atom41 atom42 atom43 atom44
    all_goals try assumption
    rw [memLoad_memStore_of_rangeApart]
    · exact atom48
    · apply RangeApart.of_toNat <;> bv_omega
  · close_resume []
    all_goals try assumption

@[refine_layout] def testMsg (fr : Activation) : Micro.Step where
  entry := .l1005e4
  exit := .l1005e8
  pre := basic fr ++ [.gpr 0 0]
  post := basic fr
  writes := []

@[refine_layout] def zeroMsg (fr : Activation) : Micro.Step where
  entry := .l1005e8
  exit := .l1005ea
  pre := basic fr
  post := basic fr ++ [.low 0 8 0]
  writes := []

theorem testMsgValid (fr : Activation) : Micro.Valid (testMsg fr) := by
  unfold Micro.Valid
  refine_one [Micro.program,testMsg]
  all_goals first | rfl | assumption | contradiction

theorem zeroMsgValid (fr : Activation) : Micro.Valid (zeroMsg fr) := by
  unfold Micro.Valid
  refine_one [Micro.program,zeroMsg]
  all_goals first | rfl | assumption

end ChaCha20Poly1305.Proofs.Decrypt.Detached
