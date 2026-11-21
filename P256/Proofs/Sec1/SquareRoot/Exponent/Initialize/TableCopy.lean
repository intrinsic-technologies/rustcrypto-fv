import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ParameterCopy

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def TableCopyPlan (offset target : Nat) : Prop :=
  Extracted.textBytes.toListFrom (offset+0) 5 =
    0x48 :: 0x8b :: (AddrMode.sib 4 none 0 (.d8 40)).modrm 0 :: (AddrMode.sib 4 none 0 (.d8 40)).tail ∧
  Extracted.textBytes.toListFrom (offset+5) 8 =
    0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+24)))).modrm 0 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+24)))).tail ∧
  Extracted.textBytes.toListFrom (offset+13) 5 =
    0x48 :: 0x8b :: (AddrMode.sib 4 none 0 (.d8 32)).modrm 0 :: (AddrMode.sib 4 none 0 (.d8 32)).tail ∧
  Extracted.textBytes.toListFrom (offset+18) 8 =
    0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+16)))).modrm 0 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+16)))).tail ∧
  Extracted.textBytes.toListFrom (offset+26) 5 =
    0x48 :: 0x8b :: (AddrMode.sib 4 none 0 (.d8 16)).modrm 0 :: (AddrMode.sib 4 none 0 (.d8 16)).tail ∧
  Extracted.textBytes.toListFrom (offset+31) 5 =
    0x48 :: 0x8b :: (AddrMode.sib 4 none 0 (.d8 24)).modrm 1 :: (AddrMode.sib 4 none 0 (.d8 24)).tail ∧
  Extracted.textBytes.toListFrom (offset+36) 8 =
    0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+8)))).modrm 1 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+8)))).tail ∧
  Extracted.textBytes.toListFrom (offset+44) 8 =
    0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+0)))).modrm 0 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 (target+0)))).tail

instance (offset target : Nat) : Decidable (TableCopyPlan offset target) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def tableCopyMemory (s : RamState) (memory : Ram) (target : Nat) : Ram :=
  [24,16,8,0].foldl (fun m j ↦ memStore m
    (exponentFrameBase s+BitVec.ofNat 64 (target+j))
    (memLoad memory (exponentFrameBase s+BitVec.ofNat 64 (16+j)) 64)) memory

def tableCopyComponents (s : RamState) (target : Nat) : List Component :=
  [.reg 0,.reg 1,.rip,.mem (exponentFrameBase s+BitVec.ofNat 64 target) 32]

theorem copy_table [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t)
    (offset target : Nat) (lo : 160≤target) (hi : target+32≤672)
    (bound : offset+52<118431) (code : TableCopyPlan offset target)
    (rip : t.RIP=Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 8 t u ∧ Frame s u ∧
      u.RIP=Extracted.textAddress+BitVec.ofNat 64 (offset+52) ∧
      AgreesExcept (tableCopyComponents s target) t u ∧
      u.external=tableCopyMemory s t.external target := by
  obtain ⟨c1,c2,c3,c4,c5,c6,c7,c8⟩ := code
  have l8 (d : BitVec 8) : (AddrMode.sib 4 none 0 (.d8 d)).tail.length=2 := rfl
  have l32 (d : BitVec 32) : (AddrMode.sib 4 none 0 (.d32 d)).tail.length=5 := rfl
  have addr1 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 40)).addr t next=
      exponentFrameBase s+BitVec.ofNat 64 40 := by
    change stackPtr t+40#64=_
    rw [hf.rsp]
    rfl
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_load_r64 ctx.outerBoundary hf
    (offset+0) 0x48 0 (.sib 4 none 0 (.d8 40))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using rip) (by change offset+0+5<118431; omega)
    c1 (by
      rw [addr1]
      have h := ScalarFrame.stack_readable ctx.toCalleePre hf (offset := 40) (len := 8) (by decide) (by decide)
      have sp : stackPtr t=exponentFrameBase s := hf.rsp
      rwa [sp] at h)
  change AgreesExcept [.reg 0,.rip] t t1 at g1
  have val1 := v1
  rw [addr1] at val1
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_store_r64 ctx.toCalleePre f1
    (offset+5) (target+24) (.d32 (BitVec.ofNat 32 (target+24)))
    0x48 0 (by simp [RexWPrefix]) rfl rfl (signExtend32_offset (by omega)) (by omega)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip1) (by change offset+5+8<118431; omega) c2
  have memory2 : t2.external=memStore t1.external
      (exponentFrameBase s+BitVec.ofNat 64 (target+24))
      (memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 40) 64) :=
    m2.trans (congrArg (memStore t1.external _) (val1))
  have addr3 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 32)).addr t2 next=
      exponentFrameBase s+BitVec.ofNat 64 32 := by
    change stackPtr t2+32#64=_
    rw [f2.rsp]
    rfl
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_load_r64 ctx.outerBoundary f2
    (offset+13) 0x48 0 (.sib 4 none 0 (.d8 32))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip2) (by change offset+13+5<118431; omega)
    c3 (by
      rw [addr3]
      have h := ScalarFrame.stack_readable ctx.toCalleePre f2 (offset := 32) (len := 8) (by decide) (by decide)
      have sp : stackPtr t2=exponentFrameBase s := f2.rsp
      rwa [sp] at h)
  change AgreesExcept [.reg 0,.rip] t2 t3 at g3
  have val3 : (Operand.reg 0 : Operand 64).read t3=
      memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 32) 64 := by
    rw [addr3] at v3
    apply v3.trans
    change memLoad t2.external _ 64 = _
    simp only [m2,m1]
    repeat rw [memLoad_memStore_rangeApart _ _ _ _ 64
      (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_store_r64 ctx.toCalleePre f3
    (offset+18) (target+16) (.d32 (BitVec.ofNat 32 (target+16)))
    0x48 0 (by simp [RexWPrefix]) rfl rfl (signExtend32_offset (by omega)) (by omega)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip3) (by change offset+18+8<118431; omega) c4
  have memory4 : t4.external=memStore t3.external
      (exponentFrameBase s+BitVec.ofNat 64 (target+16))
      (memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 32) 64) :=
    m4.trans (congrArg (memStore t3.external _) (val3))
  have addr5 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 16)).addr t4 next=
      exponentFrameBase s+BitVec.ofNat 64 16 := by
    change stackPtr t4+16#64=_
    rw [f4.rsp]
    rfl
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_load_r64 ctx.outerBoundary f4
    (offset+26) 0x48 0 (.sib 4 none 0 (.d8 16))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip4) (by change offset+26+5<118431; omega)
    c5 (by
      rw [addr5]
      have h := ScalarFrame.stack_readable ctx.toCalleePre f4 (offset := 16) (len := 8) (by decide) (by decide)
      have sp : stackPtr t4=exponentFrameBase s := f4.rsp
      rwa [sp] at h)
  change AgreesExcept [.reg 0,.rip] t4 t5 at g5
  have val5 : (Operand.reg 0 : Operand 64).read t5=
      memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 16) 64 := by
    rw [addr5] at v5
    apply v5.trans
    change memLoad t4.external _ 64 = _
    simp only [m4,m3,m2,m1]
    repeat rw [memLoad_memStore_rangeApart _ _ _ _ 64
      (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
  have addr6 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 24)).addr t5 next=
      exponentFrameBase s+BitVec.ofNat 64 24 := by
    change stackPtr t5+24#64=_
    rw [f5.rsp]
    rfl
  obtain ⟨t6,a6,f6,ip6,v6,g6,m6⟩ := frame_load_r64 ctx.outerBoundary f5
    (offset+31) 0x48 1 (.sib 4 none 0 (.d8 24))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip5) (by change offset+31+5<118431; omega)
    c6 (by
      rw [addr6]
      have h := ScalarFrame.stack_readable ctx.toCalleePre f5 (offset := 24) (len := 8) (by decide) (by decide)
      have sp : stackPtr t5=exponentFrameBase s := f5.rsp
      rwa [sp] at h)
  change AgreesExcept [.reg 1,.rip] t5 t6 at g6
  have val6 : (Operand.reg 1 : Operand 64).read t6=
      memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 24) 64 := by
    rw [addr6] at v6
    apply v6.trans
    change memLoad t5.external _ 64 = _
    simp only [m5,m4,m3,m2,m1]
    repeat rw [memLoad_memStore_rangeApart _ _ _ _ 64
      (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
  obtain ⟨t7,a7,f7,ip7,v7,g7,m7⟩ := frame_store_r64 ctx.toCalleePre f6
    (offset+36) (target+8) (.d32 (BitVec.ofNat 32 (target+8)))
    0x48 1 (by simp [RexWPrefix]) rfl rfl (signExtend32_offset (by omega)) (by omega)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip6) (by change offset+36+8<118431; omega) c7
  have memory7 : t7.external=memStore t6.external
      (exponentFrameBase s+BitVec.ofNat 64 (target+8))
      (memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 24) 64) :=
    m7.trans (congrArg (memStore t6.external _) (val6))
  obtain ⟨t8,a8,f8,ip8,v8,g8,m8⟩ := frame_store_r64 ctx.toCalleePre f7
    (offset+44) (target+0) (.d32 (BitVec.ofNat 32 (target+0)))
    0x48 0 (by simp [RexWPrefix]) rfl rfl (signExtend32_offset (by omega)) (by omega)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,l8,l32] using ip7) (by change offset+44+8<118431; omega) c8
  have memory8 : t8.external=memStore t7.external
      (exponentFrameBase s+BitVec.ofNat 64 (target+0))
      (memLoad t.external (exponentFrameBase s+BitVec.ofNat 64 16) 64) :=
    m8.trans (congrArg (memStore t7.external _) (((g6.trans g7).read (n := 64) (r := 0) (by simp)).trans val5))
  refine ⟨t8,(((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8),f8,?_,?_,?_⟩
  · simpa only [Nat.add_assoc,Nat.reduceAdd,l8,l32] using ip8
  · apply (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).widen
    · intro c hc hm
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try simp [Component.isMem] at hm
      all_goals simp [tableCopyComponents]
    · intro a c hc ha
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals
        obtain ⟨i,hi,rfl⟩ := ha
        refine ⟨.mem (exponentFrameBase s+BitVec.ofNat 64 target) 32,by simp [tableCopyComponents],?_⟩
      · exact ⟨24+i,by omega,by simp [BitVec.ofNat_add,BitVec.add_assoc]⟩
      · exact ⟨16+i,by omega,by simp [BitVec.ofNat_add,BitVec.add_assoc]⟩
      · exact ⟨8+i,by omega,by simp [BitVec.ofNat_add,BitVec.add_assoc]⟩
      · exact ⟨i,by omega,by simp [BitVec.add_assoc]⟩
  · simp only [memory8,memory7,m6,m5,memory4,m3,memory2,m1,
      tableCopyMemory,List.foldl_cons,List.foldl_nil,Nat.add_zero]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
