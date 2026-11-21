import K256.Proofs.Ecdh.Scalar.Frame
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem callSite {s : RamState} {secret key : ByteArray} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (mem : Scalar.Memory s m)
    (depth : Nat) (room : depth ≤ 10088) (below : 56 ≤ depth)
    (base : BitVec 64) (bytes : List UInt8) (off len : Nat)
    (code : ∀ b ∈ codeRange base bytes, b ∈ Extracted.programImage)
    (instruction : off + len ≤ bytes.length) (ret : BitVec 64) :
    let slot := s.regValue .rsp - BitVec.ofNat 64 depth
    let pushed := memStore m slot ret
    StoreOk Extracted.programImage m slot 8 (base + BitVec.ofNat 64 off) len ∧
      Scalar.Memory s pushed ∧ RamWriteFrame m pushed [⟨slot.toNat, 8⟩] ∧
      memLoad pushed slot 64 = ret ∧
      ∀ (k size : Nat), k + 8 ≤ depth → size ≤ k →
        Outside [⟨slot.toNat, 8⟩] (s.regValue .rsp - BitVec.ofNat 64 k) size := by
  dsimp only
  let slot := s.regValue .rsp - BitVec.ofNat 64 depth
  have writable : Writable Extracted.programImage m slot 8 :=
    (Common.stackWritable call room (by omega) (by decide)).of_frame mem.frame
  have push := ParseSignature.storeOk_of_codeRange writable code instruction
  have frame : RamWriteFrame m (memStore m slot ret) [⟨slot.toNat, 8⟩] :=
    (RamWriteFrame.refl m _).memStore _
      ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by
        have := writable.readable.low
        omega⟩
  obtain ⟨stackRoom, stackLow, _⟩ := Scalar.stack_geometry call
  have slotAddr : slot.toNat = (stackPtr s).toNat - depth :=
    Common.stackOffset call.stackAvailable room
  refine ⟨push, mem.advance call frame ?_, frame,
    memLoad_memStore_same _ _ _ (by decide) (by decide), ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ slot.toNat ∧ slot.toNat + 8 ≤ _
    rw [slotAddr]
    omega
  · intro k size above fits
    have addr := Common.stackOffset (off := k) call.stackAvailable (show k ≤ 10088 by omega)
    change (s.regValue .rsp - BitVec.ofNat 64 k).toNat = _ at addr
    unfold Outside
    rw [addr]
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change slot.toNat + 8 ≤ _
    rw [slotAddr]
    omega

end K256.Proofs.Ecdh.Wrapper
