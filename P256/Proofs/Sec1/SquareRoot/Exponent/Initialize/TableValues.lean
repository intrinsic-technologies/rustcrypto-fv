import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableState
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableCall

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

theorem tableCopyMemory_limb (s : RamState) (memory : Ram) {target j : Nat}
    (ht : target+32≤672) (hj : j<4) :
    memLoad (tableCopyMemory s memory target)
      (exponentFrameBase s+BitVec.ofNat 64 (target+8*j)) 64=
    memLoad memory (exponentFrameBase s+BitVec.ofNat 64 (16+8*j)) 64 := by
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [tableCopyMemory,List.foldl_cons,List.foldl_nil,Nat.reduceMul,Nat.reduceAdd,Nat.add_zero]
    repeat first
      | rw [memLoad_memStore_rangeApart _ _ _ _ 64
          (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
      | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem copy_table_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (h : TableState s t x n) (hn : n<16)
    (value : Field.MontgomeryAt t (exponentFrameBase s+0x10)
      (x^n%P256.Spec.Operations.domain.p))
    (offset : Nat) (hlen : offset+52<118431) (code : TableCopyPlan offset (160+32*n))
    (hip : t.RIP=Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 8 t u ∧ TableState s u x (n+1) ∧
      u.RIP=Extracted.textAddress+BitVec.ofNat 64 (offset+52) ∧
      AgreesExcept (tableCopyComponents s (160+32*n)) t u := by
  obtain ⟨u,run,frame,rip,g,mem⟩ := copy_table ctx h.frame offset (160+32*n)
    (by omega) (by omega) hlen code hip
  have old : TableState s u x n := h.of_agrees frame g (by simp [tableCopyComponents]) (by
    intro off ho c hc hcov
    simp only [tableCopyComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    have apart : RangeApart (exponentFrameBase s+BitVec.ofNat 64 (160+32*n)) 32
        (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
      RangeApart.offsets (exponentFrameBase s) (by omega) (by unfold TableDataOffset at ho; omega)
        (by unfold TableDataOffset at ho; omega)
    obtain ⟨j,hj,eq⟩ := hcov
    apply apart j hj 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm)
  have new : Field.MontgomeryAt u (exponentFrameBase s+BitVec.ofNat 64 (160+32*n))
      (x^n%P256.Spec.Operations.domain.p) := by
    apply Field.montgomeryAt_of_memLoad_limbs value.1
    · have read := ScalarFrame.stack_readable (frameOffset := 1416) ctx.toCalleePre frame
        (offset := 160+32*n) (len := 32) (by decide) (by omega)
      have sp : stackPtr u=exponentFrameBase s := frame.rsp
      rw [sp] at read
      exact read.mem
    · intro j hj
      rw [BitVec.add_assoc,← BitVec.ofNat_add,mem,tableCopyMemory_limb s _ (by omega) hj]
      simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
        value.memLoad_limb j hj
  refine ⟨u,run,{old with data := {old.data with table := ?_}},rip,g⟩
  intro i hi
  by_cases eq : i=n
  · subst i; exact new
  · exact old.data.table i (by omega)

theorem table_multiply_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x i : Nat}
    (ctx : ExponentPre s boundary x) (h : TableState s t x (i+1)) (hi : i<15)
    (offset : Nat) (disp : BitVec 32) (bound : offset+5<118431)
    (code : Extracted.textBytes.toListFrom offset 5=encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5 (disp.signExtend 64)=0x1145e0)
    (rip : t.RIP=Extracted.textAddress+BitVec.ofNat 64 offset)
    (left : t.regValue .rsi=exponentFrameBase s+BitVec.ofNat 64 (160+32*i))
    (right : t.regValue .rdx=exponentFrameBase s+0x2f8)
    (destination : t.regValue .rdi=exponentFrameBase s+0x10)
    (modulus : t.regValue .rcx=s.regValue .rsi+32) (inverse : t.regValue .r8=1) :
    ∃ u fuel, Advances boundary fuel t u ∧ TableState s u x (i+1) ∧
      u.RIP=Extracted.textAddress+BitVec.ofNat 64 (offset+5) ∧
      Field.MontgomeryAt u (exponentFrameBase s+0x10)
        (x^(i+1)%P256.Spec.Operations.domain.p) ∧
      (∀ off len : Nat, 48≤off → off+len≤1368 → ∀ j<len,
        u.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]?=
        t.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]?) := by
  obtain ⟨u,fuel,run,frame,rip,product,regs,bytes⟩ := table_call ctx h.frame hi offset disp
    bound code target rip left right destination modulus inverse (h.data.table i (by omega)) h.data.input
  have data : TableData s u x (i+1) := h.data.of_bytes (by
    intro off ho
    have v := bytes off 1 (by unfold TableDataOffset at ho; omega)
      (by unfold TableDataOffset at ho; omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using v)
  refine ⟨u,fuel,run,⟨frame,data,(regs .r14 (by simp )).trans h.bitCount,
    (regs .r15 (by simp )).trans h.parameter,
    (regs .rbx (by simp )).trans h.input,
    (regs .r12 (by simp )).trans h.inverse,
    (regs .r13 (by simp )).trans h.negativeInverse,
    (regs .rbp (by simp )).trans h.output⟩,rip,?_,bytes⟩
  simpa only [Nat.pow_succ,Nat.mod_mul_mod] using product

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
