import P256.Proofs.Program.Compare.Instructions.Common
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy1_run_of_modrm_at [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (op modrm : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (dec form : X86.Runtime.SpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = some (dec.run u))
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → dec.run a = form.run u) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some (form.run (afterFetches (beforeFetch s) (j + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (j + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) hfeatures]

end P256.Proofs.Program.Compare
