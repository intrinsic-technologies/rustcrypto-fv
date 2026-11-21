import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Ecdh.Wrapper.AffineMemory
import K256.Proofs.Ecdh.Wrapper.Child
import K256.Proofs.Ecdh.Affine.State
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

abbrev affineMemory (s : RamState) (m : Ram) := memStore m (returnSlot s) (0x101b0d : BitVec 64)

abbrev affineActivation (s : RamState) (a : Vector Value Reg.count) (m : Ram) :=
  childActivation s (affineMemory s m) (affineArgs a (localSp s)) 976 0x101b0d

theorem affineSource (s : RamState) (a : Vector Value Reg.count) (m : Ram) : (affineActivation s a m).rsi = localSp s + 344 := by
  have h : (affineArgs a (localSp s))[6] = ⟨64, localSp s + 344⟩ := by simp [affineArgs]
  change ((affineArgs a (localSp s))[6]).get 64 = _
  rw [h]
  rfl

theorem affineDest (s : RamState) (a : Vector Value Reg.count) (m : Ram) : (affineActivation s a m).rdi = localSp s + 4184 := by
  have h : (affineArgs a (localSp s))[7] = ⟨64, localSp s + 4184⟩ := by simp [affineArgs]
  change ((affineArgs a (localSp s))[7]).get 64 = _
  rw [h]
  rfl

theorem affineEntry {s : RamState} {secret peer : ByteArray} {a : Vector Value Reg.count} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (frame : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (df : a[22] = ⟨1, 0⟩)
    (gp : ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,8,9,12,13,15] → a[i].width = 64)
    (mx : a[39].width = 32) (ft : a[50].width = 16) (fc : a[51].width = 16) :
    Ecdh.Affine.CallState .l10fe50 (affineActivation s a m) (affineArgs a (localSp s))
      (affineMemory s m) := by
  have pushed := callPushFrame (0x101b0d : BitVec 64) call frame
  have regs : ChildRegisters s (affineArgs a (localSp s)) := by
    constructor
    · simp [affineArgs]
      exact localSp_sub_eight s
    · simpa [affineArgs, Vector.getElem_set] using df
    · intro i hi
      simp only [affineArgs, Fin.getElem_fin, Vector.getElem_set]
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      exact gp i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at *; omega)
    · simpa [affineArgs, Vector.getElem_set] using mx
    · simpa [affineArgs, Vector.getElem_set] using ft
    · simpa [affineArgs, Vector.getElem_set] using fc
  have slot : memLoad (affineMemory s m) (returnSlot s) 64 = 0x101b0d :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have atoms := childEntryAtoms call pushed Generate.LIR.Fn10fe50.frameInfo rfl
    (by decide) (by decide) regs (by decide : (0x101b0d : BitVec 64).toNat < 2^32) slot
  refine ⟨atoms, loaded_of_stackFrame call pushed, ?_, ?_, ?_, ?_, ?_, .refl _ _⟩
  · rw [affineSource, show localSp s + 344 = s.regValue .rsp - 5808 by unfold localSp; bv_omega]
    exact ((Common.stackWritable (off := 5808) (len := 120) call (by decide) (by decide) (by decide)).of_frame pushed).readable
  · rw [affineDest, show localSp s + 4184 = s.regValue .rsp - 1968 by unfold localSp; bv_omega]
    exact (Common.stackWritable (off := 1968) call (by decide) (by decide) (by decide)).of_frame pushed
  · rw [affineSource]
    change localSp s + 344 = returnSlot s + 352
    unfold localSp returnSlot
    bv_omega
  · rw [affineDest]
    change localSp s + 4184 = returnSlot s + 4192
    unfold localSp returnSlot
    bv_omega
  · change (s.regValue .rsp - 6160).toNat + 4280 ≤ _
    have eq := Common.stackOffset (off := 6160) call.stackAvailable (by decide)
    change (s.regValue .rsp - 6160).toNat = (s.regValue .rsp).toNat - 6160 at eq
    have low := call.stackAvailable.1
    change (s.regValue .rsp).toNat - 10088 + ((s.regValue .rsp).toNat + 8 -
      ((s.regValue .rsp).toNat - 10088)) < 2^32 at low
    omega

end K256.Proofs.Ecdh.Wrapper
