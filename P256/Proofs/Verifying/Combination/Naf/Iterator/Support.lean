import P256.Proofs.Verifying.Combination.Naf.Iterator.Interface
import P256.Proofs.Program.State
import P256.Proofs.Program.Code
import P256.Proofs.Program.Stack
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem calleeResult_of_advances [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve fuel : Nat} {components : List Component}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (execution : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept components s t)
    (rip : t.RIP = (X86Proofs.returnBoundary s).rip)
    (rsp : t.regValue .rsp = (X86Proofs.returnBoundary s).rsp)
    (registers : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      t.regValue r = s.regValue r)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi outputBytes, Stack.region s reserve])
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    CalleeResult s t boundary outputBytes reserve :=
  ⟨⟨fuel, execution⟩, rip, rsp,
    bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees,
    registers, agrees.directionFlagClear hdf pre.directionFlag,
    agrees.mxcsr hmxcsr, agrees.fcw hfcw,
    frame, ScalarFrame.loaded_of_frame pre frame, agrees.grow⟩

theorem stackRegion_contains_sub {s : RamState} {reserve offset len : Nat}
    (hReserve : Stack.NoUnderflow s reserve) (hOffset : offset ≤ reserve)
    (hLen : len ≤ offset) {address : BitVec 64}
    (hCover : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers address) :
    (Stack.region s reserve).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCover
  have hsp := (stackPtr s).isLt
  change reserve ≤ (stackPtr s).toNat at hReserve
  have ho : offset < 2^64 := by omega
  have hsub : (BitVec.ofNat 64 offset) ≤ stackPtr s := by
    simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho] using
      Nat.le_trans hOffset hReserve
  have hi64 : i < 2^64 := by omega
  have hsum : (stackPtr s).toNat - offset + i < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hsub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
    Nat.mod_eq_of_lt hsum]
  change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset + i ∧
    (stackPtr s).toNat - offset + i < (stackPtr s).toNat - reserve +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - reserve))
  omega

end P256.Proofs.Verifying.Combination.Naf.Iterator
