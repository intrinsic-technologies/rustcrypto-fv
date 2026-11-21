import P256.Proofs.Common.Memory.Fill.Stos.Spec
import X86Proofs.Instructions.Movs.Operation
import X86Proofs.Program.ReadWrite.Stack

set_option autoImplicit false

namespace P256.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem stos_operation [Bindings] (t : RamState) (h : DataReady t) (hmode : In64BitMode t)
    (bytes : Nat) (hbytes : bytes = 1 ∨ bytes = 8) (ctx : Instruction_Context)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hdst : (rdi.read t).toNat + bytes ≤ 2^32)
    (_hdstPage : (rdi.read t).toNat % 4096 + bytes ≤ 4096)
    (hdstMem : ∀ i < bytes, (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.STORE_STRING 64 (8 * bytes) ctx).run t =
      (.ok (), stosSpec bytes t) := by
  have hn : 8 * bytes = 8 ∨ 8 * bytes = 16 ∨ 8 * bytes = 32 ∨ 8 * bytes = 64 := by
    rcases hbytes with rfl | rfl <;> simp
  have hdiv : 8 * bytes / 8 = bytes := by omega
  have hwrite := logicalMemWrite_run t h false (rdi.read t) (8 * bytes) hn
    ((Operand.reg 0 : Operand (8 * bytes)).read t)
    (by simpa only [hdiv] using hdst)
    (by simpa only [hdiv] using hdstMem)
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = 0 from hdf]
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
  rcases hbytes with rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (rax_run t)]
    refine (specM_bind_run _ _ (by simp only [X86.Runtime.CheckedSlice.read, x86_runtime]; rfl)).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    rw [← BitVec.setWidth_eq_extractLsb' (by decide)]
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [stosSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess]
    rfl

end P256.Proofs.Common.Memory.Fill.Stos
