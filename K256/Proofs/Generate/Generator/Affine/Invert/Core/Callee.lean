import K256.Proofs.Generate.Generator.Affine.Invert.Core.State

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

theorem stackImage {m p : Ram} {lo : Word} {len : Nat}
    (w : Writable Extracted.programImage m lo len) (fr : RamWriteFrame m p [⟨lo.toNat,len⟩])
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) :
    ∀ b ∈ Extracted.programImage, p[b.1]? = some b.2 := by
  intro b hb
  apply (fr.outside b.1 ?_).trans (image b hb)
  refine ⟨by have := b.1.isLt; omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  change b.1.toNat + 1 ≤ lo.toNat ∨ lo.toNat + len ≤ b.1.toNat
  apply Classical.byContradiction
  intro hx
  have l : lo.toNat ≤ b.1.toNat := by omega
  apply w.notCode b hb (b.1.toNat - lo.toNat) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ - _) (by have := b.1.isLt; omega),
    Nat.add_sub_cancel' (by omega), Nat.mod_eq_of_lt b.1.isLt]

structure CalleeFrame (a : Registers) (m : Ram) (sp dst ret : Word) (depth len : Nat) : Prop where
  rsp : a[4] = ⟨64, sp⟩
  rdi : a[7] = ⟨64, dst⟩
  df : a[22] = ⟨1, 0⟩
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2
  depthBound : depth ≤ sp.toNat
  aligned : sp.toNat % 16 = 8
  returnSlot : Readable m sp 8
  retAddr : memLoad m sp 64 = ret
  retLow : ret.toNat < 2^32
  stack : Writable Extracted.programImage m (sp - BitVec.ofNat 64 depth) depth
  output : Writable Extracted.programImage m dst len
  apart : dst.toNat + len ≤ sp.toNat - depth ∨ sp.toNat + 8 ≤ dst.toNat

structure CalleeResult (a : Registers) (m : Ram) (sp dst ret : Word) (depth len : Nat)
    (out : Output Value Ram Reg.count) : Prop where
  returned : out.tag = some ⟨64, ret⟩
  rsp : out.values[4] = ⟨64, sp + 8⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15] →
    a[i].width = 64 → out.values[i] = a[i]
  controls : ∀ i : Fin Reg.count, i.val ∈ [22, 39, 50, 51] → out.values[i] = a[i]
  frame : RamWriteFrame m out.store [⟨(sp - BitVec.ofNat 64 depth).toNat, depth⟩, ⟨dst.toNat, len⟩]

structure SignedSource (m : Ram) (sp dst addr : Word) (depth len : Nat) (x : Int) : Prop where
  read : Readable m addr 33
  stackApart : addr.toNat + 33 ≤ sp.toNat - depth ∨ sp.toNat ≤ addr.toNat
  outputApart : addr.toNat + 33 ≤ dst.toNat ∨ dst.toNat + len ≤ addr.toNat
  signed : signedAt m addr x

structure LinearArgs (a : Registers) (m : Ram) (sp dst : Word) (depth len : Nat)
    (x y : Int) (u v : Word) : Prop where
  left : SignedSource m sp dst (a[6].get 64) depth len x
  right : SignedSource m sp dst (a[2].get 64) depth len y
  coeffLeft : a[1].get 64 = u
  coeffRight : a[8].get 64 = v

def wideSignedAt (m : Ram) (addr : Word) (x : Int) : Prop :=
  ∃ (v : Vector Word 5) (neg : Bool), WordsAt m addr 64 v ∧
    memLoad m (addr + 40) 8 = (if neg then 1 else 0) ∧
    let mag : Int := (((v[4].toNat * 2^64 + v[3].toNat) * 2^64 + v[2].toNat) * 2^64 +
      v[1].toNat) * 2^64 + v[0].toNat
    x = if neg then -mag else mag

noncomputable abbrev CalleeExec (l : Label) (a : Registers) (m : Ram) (out : Output Value Ram Reg.count) :=
  program.Exec (dialect Extracted.programImage) ⟨⟨l, a, m⟩, []⟩ out

end K256.Proofs.Generate.Generator.Affine.Invert.Core
