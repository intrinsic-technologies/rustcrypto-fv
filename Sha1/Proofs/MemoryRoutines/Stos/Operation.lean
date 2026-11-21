import Sha1.Proofs.MemoryRoutines.Stos.Model
import Sha1.Proofs.Compress.Machine.Memory
import Sha1.Proofs.Common.Instructions.MemoryWrite

namespace Sha1.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem store_string_operation [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 64) (ctx : Instruction_Context)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hdstMem : ∀ i < n / 8, (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.STORE_STRING 64 n ctx).run t = (.ok (), stosSpec n t) := by
  have hwrite := Sha1.Proofs.Common.Instructions.MemoryWrite.logicalMemWrite_run t h false (rdi.read t) n
    (hn.imp_right fun h ↦ Or.inr (Or.inr h)) ((Operand.reg 0 : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (dfBit u.RFLAGS), u) = _
    rw [hu, hdf]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  unfold X86.Instructions.Operations.STORE_STRING
  rcases hn with rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (rax_run t)]
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run t _ _ (by decide) (by decide))).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [stosSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess, ofInt_div8]

end Sha1.Proofs.MemoryRoutines.Stos
