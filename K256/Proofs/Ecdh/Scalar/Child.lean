import K256.Proofs.Ecdh.Wrapper.Child
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Frame

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

open Generate.Generator.Sample (compareChild sampleChildEntry nonzeroPreserved preservedValue)

open Wrapper (childActivation ChildRegisters)

theorem childKept {s : RamState} {a : Values Value Reg.count}
    (regs : ChildRegisters s a) (m : Ram) (window : Nat) (ret : BitVec 64)
    (i : Fin Reg.count) (hi : i.val ∈ nonzeroPreserved) :
    a[i] = preservedValue (childActivation s m a window ret) i.val := by
  have eq (v : Value) {w : Nat} (h : v.width = w) : v = ⟨w, v.get w⟩ := by
    cases v; cases h; simp [Value.get]
  obtain ⟨i, bound⟩ := i
  simp only [nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact regs.df | exact eq _ regs.mxcsr | exact eq _ regs.ftw | exact eq _ regs.fcw
                  | exact eq _ (regs.gp _ (by decide +revert))

theorem childEntry {s : RamState} {secret peer : ByteArray} {a : Values Value Reg.count} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (frame : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (regs : ChildRegisters s a) (info : FrameInfo) (slots : info.callSlots = [])
    (pos : 0 < info.window) (size : 6160 + info.window ≤ 10088)
    {ret : BitVec 64} (small : ret.toNat < 2^32) (saved : memLoad m (stackPtr s - 6160) 64 = ret) :
    Atom.All Extracted.programImage a m (info.entryAtoms (childActivation s m a info.window ret)) := by
  have top := Common.stackOffset call.stackAvailable (off := 6160) (by decide)
  change (stackPtr s - 6160).toNat = _ at top
  have low := Common.stackOffset call.stackAvailable size
  have space : 10088 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have align : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have args : ParseSignature.ArgumentWidths a := by
    intro i hi
    apply regs.gp
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    grind
  apply sampleChildEntry (base := childActivation s m a info.window ret)
    info slots pos regs.rsp (childKept regs m info.window ret) args
  · exact ((Common.stackWritable call (off := 6160) (len := 8)
      (by decide) (by decide) (by decide)).of_frame frame).readable
  · exact saved
  · exact small
  · change Writable _ m (stackPtr s - 6160 - BitVec.ofNat 64 info.window) info.window
    have wr := (Common.stackWritable call size (by omega : info.window ≤ 6160 + info.window + 8) pos).of_frame frame
    rw [BitVec.ofNat_add] at wr
    rw [BitVec.sub_sub]
    exact wr
  · change (stackPtr s - BitVec.ofNat 64 (6160 + info.window)).toNat + info.window ≤
      (stackPtr s - 6160).toNat
    rw [low, top]
    omega
  · change (stackPtr s - 6160).toNat % 16 = 8
    rw [top]
    omega

theorem childReturn {s : RamState} {m : Ram} {a : Values Value Reg.count}
    {out : Output Value Ram Reg.count} {win : Nat} {ret : BitVec 64}
    (regs : ChildRegisters s a)
    (done : Atom.All Extracted.programImage out.values out.store
      (Generate.LIR.Fn127d50.doneAt (childActivation s m a win ret))) :
    out.values[4] = ⟨64, Wrapper.localSp s⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ nonzeroPreserved → out.values[i] = a[i] := by
  have h := Generate.Generator.Sample.sampleChildReturn
    (base := childActivation s m a win ret) (a := a) (m := m) (tag := ret) done
  refine ⟨h.1.trans ?_, fun i hi => (h.2 i hi).trans (childKept regs m win ret i hi).symm⟩
  congr 1
  change stackPtr s - 6160 + 8 = stackPtr s - 6152
  bv_omega

end K256.Proofs.Ecdh.Scalar
