import K256.Proofs.Ecdh.Wrapper.Child
import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.AffineMemory

namespace K256.Proofs.Ecdh.Wrapper.Multiply

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Generate.Generator.Multiply

abbrev activation (s : RamState) (m : Ram) (a : Arguments) :=
  childActivation s m a 3800 0x101afa

theorem entry {s : RamState} {secret key : ByteArray} {a : Arguments} {m : Ram}
    {d : Nat} {peer : Projective} (call : ValidCall ecdhDiffieHellman s [secret,key])
    (mem : Scalar.Memory s m) (regs : ChildRegisters s a)
    (pair : (activation s m a).rsi = localSp s + 192)
    (table : (activation s m a).rcx = localSp s + 4184)
    (digits : (activation s m a).r9 = localSp s + 120)
    (output : (activation s m a).rdi = localSp s + 344)
    (one : (activation s m a).rdx = 1) (one' : (activation s m a).r8 = 1)
    (tag : memLoad m (returnSlot s) 64 = 0x101afa) (count : memLoad m (localSp s) 64 = 1)
    (valid : peer.valid) (point : peer.Stored m (localSp s + 192)) (scalar : ScalarAt s m 312 d) :
    PeerCoreEntry (activation s m a) a d peer := by
  have atoms := childEntryAtoms call mem.frame Generate.LIR.Fn11c880.frameInfo rfl
    (by decide) (by decide) regs (by decide : (0x101afa : BitVec 64).toNat < 2^32) tag
  have room := Scalar.stack_geometry call
  have sp : (returnSlot s).toNat = (stackPtr s).toNat - 6160 :=
    Common.stackOffset call.stackAvailable (by decide)
  have top : (activation s m a).rsp + 8 = localSp s := by unfold activation childActivation localSp; dsimp; bv_omega
  have access (k n : Nat) (fit : k ≤ 6152) (span : n ≤ 6152-k) (pos : 0 < n) :
      Writable Extracted.programImage m (localSp s + BitVec.ofNat 64 k) n := by
    rw [localOffset s k fit]
    exact (Common.stackWritable (off := 6152-k) call (by change 6152-k ≤ 10088; omega) (by omega) pos).of_frame mem.frame
  refine ⟨atoms, loaded_of_stackFrame call mem.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, one, one',
    top ▸ count, ?_, ?_, ?_, ?_, ?_, valid, pair ▸ point, ?_⟩
  · change s.regValue .rsp - 9960 = s.regValue .rsp - 6160 - 3800
    bv_omega
  · change 3800 ≤ (returnSlot s).toNat
    omega
  · change (returnSlot s).toNat + 6112 ≤ _
    omega
  · rw [pair]; unfold activation childActivation localSp; dsimp; bv_omega
  · rw [table]; unfold activation childActivation localSp; dsimp; bv_omega
  · rw [digits]; unfold activation childActivation localSp; dsimp; bv_omega
  · rw [output]; unfold activation childActivation localSp; dsimp; bv_omega
  · rw [top]
    change Readable m (localSp s) 8
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using (access 0 8 (by decide) (by decide) (by decide)).readable
  · rw [pair]; exact (access 192 152 (by decide) (by decide) (by decide)).readable
  · rw [table]; exact access 4184 1920 (by decide) (by decide) (by decide)
  · rw [digits]; exact access 120 66 (by decide) (by decide) (by decide)
  · rw [output]; exact access 344 120 (by decide) (by decide) (by decide)
  · rw [pair, show localSp s + 192 + 120 = localSp s + 312 by bv_omega]
    exact scalar

end K256.Proofs.Ecdh.Wrapper.Multiply
