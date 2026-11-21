import P256.Proofs.Common.Lift.Lemma.Reg
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Instructions.Call.Form

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs

theorem Operand.read_reg_get (t : RamState) (r : BitVec 5) (n : Nat) :
    (Operand.reg r : Operand n).read t = ((Reg.gpr r).read t).get n := by
  simp [Reg.read, Value.get, Operand.read]

theorem Operand.read_xmm_get (t : RamState) (r : BitVec 5) {n : Nat} (hn : n ≤ 128) :
    (Operand.xmm r : Operand n).read t = ((Reg.xmm r).read t).get n := by
  simp [Reg.read, Value.get, Operand.read, BitVec.setWidth_setWidth_of_le _ hn]

theorem Operand.read_df_get (t : RamState) :
    (Operand.df : Operand 1).read t = ((Reg.df).read t).get 1 := by
  simp [Reg.read, Value.get]

theorem Operand.read_mxcsr_get (t : RamState) :
    (Operand.mxcsr : Operand 32).read t = ((Reg.mxcsr).read t).get 32 := by
  simp [Reg.read, Value.get]

theorem stackPtr_get (t : RamState) : stackPtr t = ((Reg.gpr 4).read t).get 64 := by
  simp [Reg.read, Value.get, stackPtr]

theorem ofRFLAGS_eq_regs (t : RamState) :
    StatusFlags.ofRFLAGS t.RFLAGS =
      ⟨((Reg.flag .CF).read t).truth, ((Reg.flag .PF).read t).truth,
        ((Reg.flag .AF).read t).truth, ((Reg.flag .ZF).read t).truth,
        ((Reg.flag .SF).read t).truth, ((Reg.flag .OF).read t).truth⟩ := by
  simp [Reg.read, StatusFlags.get]

theorem Operand.read_mem_external (t : RamState) (a : BitVec 64) (n : Nat) :
    (Operand.mem a : Operand n).read t = memLoad t.external a n := rfl

theorem read_reg_stateOf {p : BitVec 64} {L : List Reg} {r : BitVec 5} {n : Nat} {mem : Ram}
    (s : RamState) (h : Reg.gpr r ∈ L) :
    (Operand.reg r : Operand n).read (stateOf p (entriesOf L s) mem) =
      (Operand.reg r : Operand n).read s := by
  rw [Operand.read_reg_get, Operand.read_reg_get, read_stateOf_entriesOf s h]

theorem read_mem_stateOf {p : BitVec 64} {L : List Reg} {n : Nat} (s : RamState) (a : BitVec 64) :
    (Operand.mem a : Operand n).read (stateOf p (entriesOf L s) s.external) =
      (Operand.mem a : Operand n).read s := by
  rw [Operand.read_mem_external, Operand.read_mem_external, stateOf_external]

theorem isTracked_of_mem_addrRegs {am : AddrMode} {r : Reg}
    (h : r ∈ addrRegs am) : r.isTracked = true := by
  have hb : ∀ b : BitVec 4, (Reg.gpr (b.setWidth 5)).isTracked = true := by decide
  cases am with
  | base b d => simp_all [addrRegs]
  | sib b i sc d => cases i <;> simp only [addrRegs, List.mem_cons, List.not_mem_nil,
      or_false] at h <;> rcases h with rfl | rfl <;> simp_all
  | rip d => simp [addrRegs] at h
  | abs i sc d => cases i <;> simp_all [addrRegs]

theorem addrRegs_any_isFlag (am : AddrMode) :
    (addrRegs am).any Reg.isFlag = false := by
  cases am with
  | sib b i sc d => cases i <;> rfl
  | abs i sc d => cases i <;> rfl
  | _ => rfl

theorem mem_of_addrRegsIn {am : AddrMode} {R : List Reg}
    (h : addrRegsIn am R = true) {r : Reg} (hr : r ∈ addrRegs am) : r ∈ R := by
  simp only [addrRegsIn, List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨r', hr', htr, hi⟩ := h r hr
  rwa [← Reg.ofIndex_index (isTracked_of_mem_addrRegs hr), ← Nat.eq_of_beq_eq_true hi,
    Reg.ofIndex_index htr]

theorem addr_stateOf (am : AddrMode) {p : BitVec 64} {mem : Ram}
    {R : List Reg} (s : RamState) (h : ∀ r ∈ addrRegs am, r ∈ R) (q : BitVec 64) :
    am.addr (stateOf p (entriesOf R s) mem) q = am.addr s q := by
  have hr : ∀ r ∈ addrRegs am, r.read (stateOf p (entriesOf R s) mem) = r.read s :=
    fun r hr => read_stateOf_entriesOf s (h r hr)
  cases am with
  | base b d =>
    simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get]
    rw [hr _ (by simp [addrRegs])]
  | sib b i sc d =>
    cases i <;> simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get]
    · rw [hr _ (by simp [addrRegs])]
    · rw [hr _ (by simp [addrRegs]), hr (.gpr _) (by simp [addrRegs])]
  | rip d => rfl
  | abs i sc d =>
    cases i <;> simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get]
    rw [hr _ (by simp [addrRegs])]

theorem addr_stateOf_append (am : AddrMode) {p : BitVec 64} {mem : Ram}
    (L : List Reg) (s : RamState) (q : BitVec 64) :
    am.addr (stateOf p (entriesOf (L ++ addrRegs am) s) mem) q = am.addr s q :=
  addr_stateOf am s (fun _ h => List.mem_append_right _ h) q

theorem addr_stateOf_addrRegs (am : AddrMode) {p : BitVec 64} {mem : Ram}
    (s : RamState) (q : BitVec 64) :
    am.addr (stateOf p (entriesOf (addrRegs am) s) mem) q = am.addr s q :=
  addr_stateOf am s (fun _ h => h) q

end P256.Proofs.Lift
