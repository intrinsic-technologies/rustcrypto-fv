import K256.Proofs.Signing.Composition.Attempt.State
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

abbrev inverseCopy (m : Ram) (p : BitVec 64) (w : Vector (BitVec 64) 4) :=
  memStore (memStore (memStore (memStore m (p+424) w[0]) (p+432) w[1]) (p+440) w[2]) (p+448) w[3]

abbrev savedRegs : List Nat := [5,12,13,14,15,22,39,50,51]

set_option maxHeartbeats 750000 in
theorem generatorCall {a : Registers} {m m1 m2 m3 m4 : Ram} {p : BitVec 64} {w : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = p) (rbx : a[3].get 64 = p+624) (r12 : a[12].get 64 = p+8)
    (l0 : LoadOk m (p+8) 8) (v0 : memLoad m (p+8) 64 = w[0])
    (l1 : LoadOk m (p+16) 8) (v1 : memLoad m (p+16) 64 = w[1])
    (g0 : StoreOk Extracted.programImage m (p+424) 8 0x105b2d 8)
    (s0 : memStore m (p+424) w[0] = m1)
    (g1 : StoreOk Extracted.programImage m1 (p+432) 8 0x105b35 8)
    (s1 : memStore m1 (p+432) w[1] = m2)
    (l2 : LoadOk m2 (p+24) 8) (v2 : memLoad m2 (p+24) 64 = w[2])
    (g2 : StoreOk Extracted.programImage m2 (p+440) 8 0x105b42 8)
    (s2 : memStore m2 (p+440) w[2] = m3)
    (l3 : LoadOk m3 (p+32) 8) (v3 : memLoad m3 (p+32) 64 = w[3])
    (g3 : StoreOk Extracted.programImage m3 (p+448) 8 0x105b4f 8)
    (s3 : memStore m3 (p+448) w[3] = m4)
    (push : StoreOk Extracted.programImage m4 (p-8) 8 0x105b5d 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105b23,a,m⟩ =
      .call ⟨.l10ee80,b,memStore m4 (p-8) (0x105b62 : BitVec 64)⟩ (resume .l105b62 0x105b62) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[6] = ⟨64,p+624⟩ ∧ b[7] = ⟨64,p+8⟩ ∧ b[1] = ⟨64,w[1]⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ 2 :: 3 :: 8 :: 9 :: savedRegs → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?_⟩
  case run =>
    cfg_eval [rsp,rbx,r12,l0,v0,l1,v1,g0,s0,g1,s1,l2,v2,g2,s2,l3,v3,g3,s3,push]
    rfl
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro ⟨i, hi⟩ hm
  simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem affineCall {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (r12 : a[12].get 64 = p+8)
    (push : StoreOk Extracted.programImage m (p-8) 8 0x105b70 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105b62,a,m⟩ =
      .call ⟨.l10fe50,b,memStore m (p-8) (0x105b75 : BitVec 64)⟩ (resume .l105b75 0x105b75) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[3] = ⟨64,p+256⟩ ∧ b[6] = ⟨64,p+8⟩ ∧ b[7] = ⟨64,p+256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?_⟩
  case run =>
    cfg_eval [rsp,r12,push]
    rfl
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro ⟨i, hi⟩ hm
  simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem serializeCall {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (rbx : a[3].get 64 = p+256)
    (push : StoreOk Extracted.programImage m (p-8) 8 0x105b83 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105b75,a,m⟩ =
      .call ⟨.l120350,b,memStore m (p-8) (0x105b88 : BitVec 64)⟩ (resume .l105b88 0x105b88) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[14] = ⟨64,p+160⟩ ∧ b[6] = ⟨64,p+256⟩ ∧ b[7] = ⟨64,p+160⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ 3 :: savedRegs.erase 14 → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?_⟩
  case run =>
    cfg_eval [rsp,rbx,push]
    rfl
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro ⟨i, hi⟩ hm
  change i ∈ [3,5,12,13,15,22,39,50,51] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.Composition.Attempt
