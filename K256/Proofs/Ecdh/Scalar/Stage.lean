import K256.Proofs.Ecdh.CallSite
import K256.Proofs.Ecdh.Scalar.Child
import K256.Proofs.Ecdh.Scalar.Frame
import K256.Proofs.Ecdh.Scalar.Prepare

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Wrapper

theorem childRegisters {s : RamState} {a b : Values Value Reg.count} (regs : Registers s a)
    (sp : b[4] = ⟨64, localSp s - 8⟩)
    (width : ∀ i : Fin Reg.count, a[i].width = 64 → b[i].width = 64)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]) :
    Wrapper.ChildRegisters s b := by
  refine ⟨sp.trans ?_, (keep 22 (by decide)).trans regs.df, ?_, ?_, ?_, ?_⟩
  · congr 1
    change stackPtr s - 6152 - 8 = stackPtr s - 6160
    bv_omega
  · intro i hi
    apply width
    have h : i.val ∈ Activation.argumentNumbers ∨ i.val ∈ Activation.calleeSavedNumbers := by
      simp only [Activation.argumentNumbers, Activation.calleeSavedNumbers, List.mem_cons,
        List.not_mem_nil, or_false] at hi ⊢
      grind
    exact h.elim (regs.args i) (regs.savedWidths i)
  · exact congrArg Value.width ((keep 39 (by decide)).trans regs.mx)
  · exact congrArg Value.width ((keep 50 (by decide)).trans regs.ft)
  · exact congrArg Value.width ((keep 51 (by decide)).trans regs.fc)

theorem returnedRegisters {s : RamState} {a b c : Values Value Reg.count} (regs : Registers s a)
    (pre : Wrapper.ChildRegisters s b) (sp : c[4] = ⟨64, localSp s⟩)
    (args : ParseSignature.ArgumentWidths c)
    (keep : ∀ i : Fin Reg.count, i.val ∈ Generate.Generator.Sample.nonzeroPreserved → c[i] = b[i])
    (prev : ∀ i : Fin Reg.count, i.val ∈ [3,13,14,22,39,50,51] → b[i] = a[i]) :
    Registers s c := by
  refine ⟨sp, args, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have eq := keep i (by
      simp only [Generate.Generator.Sample.nonzeroPreserved, Activation.calleeSavedNumbers,
        List.mem_cons, List.not_mem_nil, or_false] at *
      grind)
    exact (congrArg Value.width eq).trans (pre.gp i (by
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      grind))
  all_goals first
    | exact (keep 3 (by decide)).trans ((prev 3 (by decide)).trans regs.output)
    | exact (keep 14 (by decide)).trans ((prev 14 (by decide)).trans regs.peer)
    | exact (keep 13 (by decide)).trans ((prev 13 (by decide)).trans regs.r13)
    | exact (keep 22 (by decide)).trans ((prev 22 (by decide)).trans regs.df)
    | exact (keep 39 (by decide)).trans ((prev 39 (by decide)).trans regs.mx)
    | exact (keep 50 (by decide)).trans ((prev 50 (by decide)).trans regs.ft)
    | exact (keep 51 (by decide)).trans ((prev 51 (by decide)).trans regs.fc)

theorem stageMemory {s : RamState} {secret peer : ByteArray} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, peer]) (mem : Memory s m)
    (start : Nat) (ret : BitVec 64) (off : start = 0x8d8 ∨ start = 0x1058) :
    Memory s (prepareMemory m (localSp s) start ret) ∧
      memLoad (prepareMemory m (localSp s) start ret) (stackPtr s - 6160) 64 = ret := by
  let sp := localSp s
  let z := fun (n : Ram) (k : Nat) => memStore n (sp + BitVec.ofNat 64 (start + k)) (0 : BitVec 64)
  let n := z (z (z (z m 24) 16) 8) 0
  have ⟨room, limit, base⟩ := stack_geometry call
  change sp.toNat = _ at base
  have zero (ram : Ram) (older : Memory s ram) (k : Nat) (small : k ≤ 24) : Memory s (z ram k) := by
    let addr := sp + BitVec.ofNat 64 (start + k)
    have bounds : (stackPtr s).toNat - 10088 ≤ addr.toNat ∧ addr.toNat + 8 ≤ (stackPtr s).toNat - 48 := by
      change _ ≤ (sp + BitVec.ofNat 64 (start + k)).toNat ∧
        (sp + BitVec.ofNat 64 (start + k)).toNat + 8 ≤ _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rcases off with rfl | rfl <;> omega
    have writes : RamWriteFrame ram (z ram k) [⟨addr.toNat, 8⟩] := by
      apply (RamWriteFrame.refl _ _).memStore
      exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by change addr.toNat + 8 ≤ 2^64; omega⟩
    exact older.advance call writes (fun r hr => List.mem_singleton.mp hr ▸ bounds)
  have before : Memory s n :=
    zero _ (zero _ (zero _ (zero _ mem 24 (by decide)) 16 (by decide)) 8 (by decide)) 0 (by decide)
  have slot : sp - 8 = stackPtr s - 6160 := by change stackPtr s - 6152 - 8 = _; bv_omega
  change Memory s (memStore n (sp - 8) ret) ∧ memLoad (memStore n (sp - 8) ret) _ 64 = ret
  rw [slot]
  rcases off with rfl | rfl
  · have site := Wrapper.callSite call before 6160 (by decide) (by decide)
      0x1016be LIR.bytes_l1016be 79 5
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l1016be x hx)) (by decide) ret
    exact ⟨site.2.1, site.2.2.2.1⟩
  · have site := Wrapper.callSite call before 6160 (by decide) (by decide)
      0x101712 LIR.bytes_l101712 59 5
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l101712 x hx)) (by decide) ret
    exact ⟨site.2.1, site.2.2.2.1⟩

theorem preparedWords {m : Ram} {base ret : BitVec 64} {start : Nat} {w : Vector (BitVec 64) 4}
    {addr : BitVec 64} (words : WordsAt m addr 64 w)
    (win : Writable Extracted.programImage m (base - 8) (start + 40))
    (apart : Outside [⟨(base - 8).toNat, 8⟩, ⟨(base + BitVec.ofNat 64 start).toNat, 32⟩] addr 32) :
    WordsAt (prepareMemory m base start ret) addr 64 w :=
  words.of_frame (prepareMemory_frame win) (by decide) apart

end K256.Proofs.Ecdh.Scalar
