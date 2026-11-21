import K256.Proofs.ParseSignature.Wrapper.Frame
import K256.Proofs.Common.SignatureBuffers

namespace K256.Proofs.ParseSignature.Wrapper

open K256.Spec.Program K256.Proofs.Common Prelude X86 X86.Machine X86Proofs K256.Proofs.Lift K256.Proofs.Refine

theorem afterSerialize {s : RamState} {bytes : ByteArray} {m m' : Ram}
    (call : ValidCall signatureFromSlice s [bytes]) (size : bytes.size = 64)
    (stack : RamWriteFrame s.external m [Stack.region s signatureFromSlice.minStackBytes])
    (output : RamWriteFrame m m' [buffer (s.regValue .rdi) 64]) :
    let sp := s.regValue .rsp
    RamWriteFrame s.external m' [outputRegion signatureFromSlice s,
      Stack.region s signatureFromSlice.minStackBytes] ∧
    memLoad m' (sp - 8) 64 = memLoad m (sp - 8) 64 ∧ memLoad m' sp 64 = memLoad m sp 64 := by
  intro sp
  let dst := s.regValue .rdi
  let st := Stack.region s signatureFromSlice.minStackBytes
  let dest := buffer dst 64
  obtain ⟨_, hw, _, apart, _⟩ := signatureBuffers call size
  have hsep := apart.2 st List.mem_cons_self
  have room : 784 ≤ sp.toNat := call.stackAvailable.2.2.1
  have limit := call.stackAvailable.1
  change sp.toNat - 784 + (sp.toNat + 8 - (sp.toNat - 784)) < 2^32 at limit
  change dst.toNat + 64 ≤ sp.toNat - 784 ∨
    sp.toNat - 784 + (sp.toNat + 8 - (sp.toNat - 784)) ≤ dst.toNat at hsep
  have extFrame : RamWriteFrame s.external m [dest, st] :=
    (RamWriteFrame.refl s.external [dest, st]).trans stack (by
      rintro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨st, by simp, Nat.le_refl _, Nat.le_refl _⟩)
  have frame : RamWriteFrame s.external m' [dest, st] :=
    extFrame.trans output (by
      rintro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨dest, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have outside (a : BitVec 64) (lo : sp.toNat - 8 ≤ a.toNat) (hi : a.toNat ≤ sp.toNat) :
      Outside [dest] a 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change a.toNat + 8 ≤ dst.toNat ∨ dst.toNat + 64 ≤ a.toNat
    omega
  have sp8 : (sp - 8).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ sp.toNat; omega)]
    rfl
  exact ⟨frame, output.memLoad_eq (outside _ (by omega) (by omega)),
    output.memLoad_eq (outside _ (by omega) (Nat.le_refl _))⟩

end K256.Proofs.ParseSignature.Wrapper
