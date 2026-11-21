import K256.Proofs.Verify.Core.Scalars.Digest.Prepare
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Barrier

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Adapter

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def pushed (m : Ram) (x : BitVec 64) := memStore m (x+88) (0x10519d : BitVec 64)

def staged (a : Registers) (m : Ram) (x : BitVec 64) :=
  let n := memStore (pushed m x) (x+80) (a[15].get 64)
  let n := memStore n (x+72) (a[14].get 64)
  let n := memStore n (x+64) (a[13].get 64)
  let n := memStore n (x+56) (a[12].get 64)
  let n := memStore n (x+48) (a[3].get 64)
  memStore n (x-8) (0x10a0f2 : BitVec 64)

abbrev savedRegs : List Nat := [3,5,12,13,14,15,22,39,50,51]

theorem callWrapper (a : Registers) (m : Ram) (x : BitVec 64)
    (rsp : a[4].get 64 = x+96)
    (win : Writable Extracted.programImage m (x-8) 104) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10518b,a,m⟩ =
      .call ⟨.l10a0c0,b,pushed m x⟩ (Reduce.resume .l10519d 0x10519d) ∧
      b[4] = ⟨64,x+88⟩ ∧ b[6] = ⟨64,x+320⟩ ∧ b[7] = ⟨64,x+104⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i]=a[i] := by
  refine ⟨?b, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l10518b
    · rfl
  case regs =>
    refine ⟨rfl,rfl,rfl,?_⟩
    rintro ⟨i,_⟩ hi
    simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 4096 in
theorem callInverse (b : Registers) (m : Ram) (x : BitVec 64)
    (rsp : b[4].get 64 = x+88) (dst : b[7].get 64 = x+104)
    (src : b[6] = ⟨64,x+320⟩)
    (win : Writable Extracted.programImage (pushed m x) (x-8) 104) :
    ∃ c : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10a0c0,b,pushed m x⟩ =
      .call ⟨.l109490,c,staged b m x⟩ (Reduce.resume .l10a0f2 0x10a0f2) ∧
      c[4] = ⟨64,x-8⟩ ∧ c[6] = ⟨64,x+320⟩ ∧ c[7] = ⟨64,x+8⟩ ∧
      c[3] = ⟨64,x+104⟩ ∧ c[1] = ⟨64,0xb4f20099aa774ec1⟩ ∧
      c[2] = ⟨64,0x2021a0⟩ ∧ c[8] = ⟨64,0x202180⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → c[i]=b[i] := by
  refine ⟨?c, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp,dst]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10a0c0)
    rfl
  case regs =>
    refine ⟨rfl,src,rfl,rfl,rfl,rfl,rfl,?_⟩
    rintro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Scalars.Inverse.Adapter
