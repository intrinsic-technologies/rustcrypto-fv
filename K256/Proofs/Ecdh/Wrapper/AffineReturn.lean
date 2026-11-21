import K256.Proofs.Ecdh.Wrapper.AffineEntry

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.Generator.Affine

theorem affineReturnFrame {s : RamState} {secret peer : ByteArray}
    {a : Vector Value Reg.count} {m n : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, peer]) (saved : Saved s m)
    (frame : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (writes' : RamWriteFrame (affineMemory s m) n (writes (affineActivation s a m))) :
    Saved s n ∧ RamWriteFrame s.external n [Stack.region s ecdhDiffieHellman.minStackBytes] := by
  let slot : MemoryRegion := ⟨(returnSlot s).toNat, 8⟩
  have push : RamWriteFrame m (affineMemory s m) [slot] := by
    apply (RamWriteFrame.refl m [slot]).memStore
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _,
      (Common.stackRange (off := 6160) (len := 8) call.stackAvailable (by decide) (by decide)).2.2⟩
  have room : 10088 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have shift (off : Nat) (h : off ≤ 10088) :
      (s.regValue .rsp - BitVec.ofNat 64 off).toNat = (s.regValue .rsp).toNat - off :=
    Common.stackOffset call.stackAvailable h
  have top : (returnSlot s).toNat = (s.regValue .rsp).toNat - 6160 := shift 6160 (by decide)
  have keep := saved.of_frame call push (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (returnSlot s).toNat + 8 ≤ _
    omega)
  have dest : (affineActivation s a m).rdi.toNat = (s.regValue .rsp).toNat - 1968 := by
    rw [affineDest, show localSp s + 4184 = s.regValue .rsp - 1968 by unfold localSp; bv_omega]
    exact shift 1968 (by decide)
  have low : (affineActivation s a m).low.toNat = (s.regValue .rsp).toNat - 7136 :=
    shift 7136 (by decide)
  have bounds (r : MemoryRegion) (h : r ∈ writes (affineActivation s a m)) :
      (s.regValue .rsp).toNat - 10088 ≤ r.start ∧
        r.start + r.size ≤ (s.regValue .rsp).toNat - 48 := by
    rcases List.mem_cons.mp h with h|h
    · subst r
      change _ ≤ (affineActivation s a m).low.toNat ∧ (affineActivation s a m).low.toNat +
        ((returnSlot s).toNat - (affineActivation s a m).low.toNat) ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨by change _ ≤ (affineActivation s a m).rdi.toNat; omega,
        by change (affineActivation s a m).rdi.toNat + 88 ≤ _; omega⟩
  refine ⟨keep.of_frame call writes' (fun r hr => (bounds r hr).2),
    (callPushFrame 0x101b0d call frame).trans writes' ?_⟩
  intro r hr
  have b := bounds r hr
  refine ⟨_, List.mem_cons_self, b.1, ?_⟩
  change _ ≤ (s.regValue .rsp).toNat - 10088 +
    ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10088))
  omega

end K256.Proofs.Ecdh.Wrapper
