import Sha3.Proofs.Finalize.Layout
import Sha3.Proofs.Finalize.Output.Digest
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Finalize.Output

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def bytes : Variant → List UInt8
  | .sha224 => output224Bytes
  | .sha256 => output256Bytes
  | .sha384 => output384Bytes
  | .sha512 => output512Bytes

def steps : Variant → Nat
  | .sha224 | .sha256 => 8
  | .sha384 => 12
  | .sha512 => 16

def effect (v : Variant) (p ptr out : BitVec 64) : RamState → Effect :=
  match v with
  | .sha224 => output224Effect p ptr out
  | .sha256 => output256Effect p ptr out
  | .sha384 => output384Effect p ptr out
  | .sha512 => output512Effect p ptr out

structure Pre (v : Variant) (p ptr out : BitVec 64) (a : Keccak.Lanes)
    (code : CodeMap) (s : RamState) : Prop
    extends OutputPre p ptr out v.digestBytes (.reg 14) code s where
  lanes : Permutation.memoryLanes ptr s = a

structure Result (v : Variant) (p out : BitVec 64) (a : Keccak.Lanes)
    (s t : RamState) : Prop where
  rip : t.RIP = p + BitVec.ofNat 64 (outputBytes v)
  agrees : AgreesExcept (outputChanges out v.digestBytes) s t
  output : ∀ i : Fin v.digestBytes, t.external[out + BitVec.ofNat 64 i.val]? =
    some (Absorption.digestLanes a v.digestBytes (Nat.le_trans v.digestBytes_le v.rate_le))[i.val]

theorem effect_rip (v : Variant) (p ptr out : BitVec 64) (s : RamState) :
    (effect v p ptr out s).rip = p + BitVec.ofNat 64 (outputBytes v) := by
  cases v <;> rfl

theorem effect_agrees {v : Variant} {p ptr out : BitVec 64} {s t : RamState}
    (h : (effect v p ptr out s).Holds s t) :
    AgreesExcept (outputChanges out v.digestBytes) s t := by
  cases v with
  | sha224 => exact output224Effect_agrees h
  | sha256 => exact output256Effect_agrees h
  | sha384 => exact output384Effect_agrees h
  | sha512 => exact output512Effect_agrees h

theorem effect_digest {v : Variant} {p ptr out : BitVec 64} {s t : RamState}
    (a : Keccak.Lanes) (h : (effect v p ptr out s).Holds s t)
    (halloc : MemReadable s out v.digestBytes) (hlanes : Permutation.memoryLanes ptr s = a) :
    ∀ i : Fin v.digestBytes, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a v.digestBytes
        (Nat.le_trans v.digestBytes_le v.rate_le))[i.val] := by
  cases v with
  | sha224 => exact output224Effect_digest a h halloc hlanes
  | sha256 => exact output256Effect_digest a h halloc hlanes
  | sha384 => exact output384Effect_digest a h halloc hlanes
  | sha512 => exact output512Effect_digest a h halloc hlanes

theorem effect_advance [Bindings] (v : Variant) (p ptr out : BitVec 64)
    (boundary : ReturnBoundary) (code : CodeMap)
    (hcode : ∀ x ∈ codeRange p (bytes v), x ∈ code)
    (hboundary : ∀ offset ≤ outputBytes v, p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (steps v) (OutputPre p ptr out v.digestBytes (.reg 14) code) code
      (Effect.post (effect v p ptr out)) := by
  cases v with
  | sha224 =>
    apply output224_advance p ptr out boundary code hcode
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hboundary _ (by decide +kernel)
  | sha256 =>
    apply output256_advance p ptr out boundary code hcode
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hboundary _ (by decide +kernel)
  | sha384 =>
    apply output384_advance p ptr out boundary code hcode
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hboundary _ (by decide +kernel)
  | sha512 =>
    apply output512_advance p ptr out boundary code hcode
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> exact hboundary _ (by decide +kernel)

theorem copy_at [Bindings] (v : Variant) (p ptr out : BitVec 64) (a : Keccak.Lanes)
    (boundary : ReturnBoundary) (code : CodeMap)
    (hcode : ∀ x ∈ codeRange p (bytes v), x ∈ code)
    (hboundary : ∀ offset ≤ outputBytes v, p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (steps v) (Pre v p ptr out a code) code (Result v p out a) := by
  apply (effect_advance v p ptr out boundary code hcode hboundary).conseq
  · exact fun _ hp ↦ hp.toOutputPre
  · intro s t hp he
    refine ⟨he.rip.trans (effect_rip v p ptr out s), effect_agrees he, ?_⟩
    exact effect_digest a he (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        hp.outputRead 0 v.digestBytes (Nat.zero_add _ ▸ Nat.le_refl _)) hp.lanes

theorem image (v : Variant) (reset : Bool) (keccak : Bool := false) :
    ∀ x ∈ codeRange (outputAddress v reset keccak) (bytes v), x ∈ Extracted.programImage := by
  cases keccak
  · cases v <;> cases reset
    · exact textSlice_subset_programImage (offset := 0x6513) (len := 29)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6573) (len := 29)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6893) (len := 30)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x68f3) (len := 30)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6960) (len := 46)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x69d0) (len := 46)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x65e0) (len := 62)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6660) (len := 62)
        (by decide +kernel) (by decide +kernel)

  · cases v <;> cases reset
    · exact textSlice_subset_programImage (offset := 0x66f3) (len := 29)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6753) (len := 29)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x67c3) (len := 30)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6823) (len := 30)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6260) (len := 46)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x62d0) (len := 46)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x6350) (len := 62)
        (by decide +kernel) (by decide +kernel)
    · exact textSlice_subset_programImage (offset := 0x63d0) (len := 62)
        (by decide +kernel) (by decide +kernel)

theorem inProgram_output (v : Variant) (reset : Bool) (offset : Nat)
    (h : offset ≤ outputBytes v) (keccak : Bool := false) :
    InProgram (outputAddress v reset keccak + BitVec.ofNat 64 offset) := by
  have hp : outputAddress v reset keccak = Extracted.textAddress +
      BitVec.ofNat 64 ((outputAddress v reset keccak).toNat - Extracted.textAddress.toNat) := by
    cases v <;> cases reset <;> cases keccak <;> decide +kernel
  have hsize : (outputAddress v reset keccak).toNat - Extracted.textAddress.toNat +
      outputBytes v < Extracted.textBytes.size := by
    cases v <;> cases reset <;> cases keccak <;> decide +kernel
  rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Permutation.inProgram_text_offset _ (by omega)

theorem copy [Bindings] (v : Variant) (reset : Bool) (ptr out : BitVec 64)
    (a : Keccak.Lanes) (boundary : ReturnBoundary) (hboundary : ¬ InProgram boundary.rip) (keccak : Bool := false) :
    AdvanceTriple boundary (steps v)
      (Pre v (outputAddress v reset keccak) ptr out a Extracted.programImage) Extracted.programImage
      (Result v (outputAddress v reset keccak) out a) :=
  copy_at v (outputAddress v reset keccak) ptr out a boundary Extracted.programImage (image v reset keccak)
    (fun offset ho he ↦ hboundary (he ▸ inProgram_output v reset offset ho keccak))

theorem Result.stack {v : Variant} {p out : BitVec 64} {a : Keccak.Lanes} {s t : RamState}
    (h : Result v p out a s t) : stackPtr t = stackPtr s := outputChanges_stack h.agrees

theorem Result.bytes {v : Variant} {p out : BitVec 64} {a : Keccak.Lanes} {s t : RamState}
    (h : Result v p out a s t) : Bytes t.external out v.digestBytes
      (fun i ↦ ((Absorption.digestLanes a v.digestBytes
        (Nat.le_trans v.digestBytes_le v.rate_le)).toArray[i]?).getD 0) := by
  intro i hi
  have hi' : i < (Absorption.digestLanes a v.digestBytes
      (Nat.le_trans v.digestBytes_le v.rate_le)).toArray.size := by
    simpa only [Vector.size_toArray] using hi
  simpa only [Array.getElem?_eq_getElem hi', Option.getD_some, Vector.getElem_toArray] using
    h.output ⟨i, hi⟩

end Sha3.Proofs.Finalize.Output
