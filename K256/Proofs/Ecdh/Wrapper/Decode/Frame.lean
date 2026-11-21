import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.AffineEntry
import K256.Proofs.Ecdh.LIR.Fn120f30.Frame
import K256.Proofs.Sec1.Serialize.Layout

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR

abbrev decoderActivation (s : RamState) (m : Ram) (a : Arguments) :=
  childActivation s m a 1464 0x101823

private theorem localNat {s : RamState} {secret peer : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret,peer]) (off : Nat) (h : off ≤ 6152) :
    (localSp s + BitVec.ofNat 64 off).toNat = (s.regValue .rsp).toNat - (6152-off) := by
  rw [localOffset _ _ h]
  exact Common.stackOffset call.stackAvailable (by change 6152 - off ≤ 10088; omega)

theorem decoderEntry {s : RamState} {secret peer : ByteArray} {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret,peer]) (mem : Scalar.Memory s m)
    (regs : ChildRegisters s a)
    (src : a[6].get 64 = localSp s + 48) (dst : a[7].get 64 = localSp s + 344)
    (slot : memLoad m (returnSlot s) 64 = 0x101823) :
    let fr := decoderActivation s m a
    Atom.All Extracted.programImage a m (Fn120f30.frameAt .l120f30 fr) ∧
    Readable m fr.rsi 33 ∧ Writable Extracted.programImage m fr.rdi 89 ∧
    fr.rsp.toNat + 8 ≤ fr.rsi.toNat ∧ fr.rsp.toNat + 8 ≤ fr.rdi.toNat ∧
    (fr.rsp.toNat ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat - 1464) := by
  dsimp only
  have atoms := childEntryAtoms call mem.frame Fn120f30.frameInfo rfl
    (by decide) (by decide) regs (by decide : (0x101823 : BitVec 64).toNat < 2^32) slot
  refine ⟨atoms, ?_, ?_, ?_, ?_, ?_⟩
  · change Readable m (a[6].get 64) 33
    rw [src, show localSp s + 48 = s.regValue .rsp - 6104 from localOffset s 48 (by decide)]
    exact ((Common.stackWritable (off := 6104) call (by decide) (by decide) (by decide)).of_frame mem.frame).readable
  · change Writable _ m (a[7].get 64) 89
    rw [dst, show localSp s + 344 = s.regValue .rsp - 5808 from localOffset s 344 (by decide)]
    exact (Common.stackWritable (off := 5808) call (by decide) (by decide) (by decide)).of_frame mem.frame
  all_goals
    have depth : 10088 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
    have top : (decoderActivation s m a).rsp.toNat = (s.regValue .rsp).toNat - 6160 :=
      Common.stackOffset (off := 6160) call.stackAvailable (by decide)
  · rw [top]; change _ ≤ (a[6].get 64).toNat
    rw [src, show (localSp s + 48).toNat = (s.regValue .rsp).toNat - 6104 from localNat call 48 (by decide)]; omega
  · rw [top]; change _ ≤ (a[7].get 64).toNat
    rw [dst, show (localSp s + 344).toNat = (s.regValue .rsp).toNat - 5808 from localNat call 344 (by decide)]; omega
  · have win := Common.stackWritable (off := 10088) (len := 10088) call (by decide) (by decide) (by decide)
    have apart := Sec1.Serialize.writable_text_apart win (by decide)
    have low : (s.regValue .rsp - 10088).toNat = (s.regValue .rsp).toNat - 10088 :=
      Common.stackOffset (off := 10088) call.stackAvailable (by decide)
    change (s.regValue .rsp - 10088).toNat + 10088 ≤ _ ∨ _ ≤ (s.regValue .rsp - 10088).toNat at apart
    omega

theorem decoderMemory {s : RamState} {secret peer : ByteArray} {a : Arguments} {m n : Ram} {d : Nat}
    (call : ValidCall ecdhDiffieHellman s [secret,peer]) (mem : Scalar.Memory s m)
    (scalar : ScalarAt s m 16 d) (dst : a[7].get 64 = localSp s + 344)
    (frame : RamWriteFrame m n [(decoderActivation s m a).region,⟨(a[7].get 64).toNat,89⟩]) :
    Scalar.Memory s n ∧ ScalarAt s n 16 d := by
  let fr := decoderActivation s m a
  have depth : 10088 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have top : fr.rsp.toNat = (s.regValue .rsp).toNat - 6160 :=
    Common.stackOffset (off := 6160) call.stackAvailable (by decide)
  have low : fr.low.toNat = (s.regValue .rsp).toNat - 7624 :=
    Common.stackOffset (off := 7624) call.stackAvailable (by decide)
  have dn : (a[7].get 64).toNat = (s.regValue .rsp).toNat - 5808 :=
    (congrArg BitVec.toNat dst).trans (localNat call 344 (by decide))
  constructor
  · apply mem.advance call frame
    intro r hr
    rcases List.mem_cons.mp hr with eq|hr
    · subst r
      change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat) ≤ _
      change (s.regValue .rsp).toNat - 10088 ≤ _ ∧ _ ≤ (s.regValue .rsp).toNat - 48
      omega
    · obtain rfl := List.mem_singleton.mp hr
      change (s.regValue .rsp).toNat - 10088 ≤ (a[7].get 64).toNat ∧ (a[7].get 64).toNat + 89 ≤ (s.regValue .rsp).toNat - 48
      omega
  · apply WordsAt.of_frame scalar frame (by decide)
    have pos := localNat call 16 (by decide)
    have limit := (Scalar.stack_geometry call).2.1
    change (s.regValue .rsp).toNat + 8 < 2^32 at limit
    constructor
    · change (localSp s + BitVec.ofNat 64 16).toNat + 32 ≤ _
      omega
    · intro r hr
      rcases List.mem_cons.mp hr with eq|hr
      · subst r
        right
        change fr.low.toNat + (fr.rsp.toNat-fr.low.toNat) ≤ _
        omega
      · obtain rfl := List.mem_singleton.mp hr
        left
        change (localSp s + BitVec.ofNat 64 16).toNat + 32 ≤ (a[7].get 64).toNat
        omega

end K256.Proofs.Ecdh.Wrapper
