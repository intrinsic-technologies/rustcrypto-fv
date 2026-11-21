import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Y
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.XFinished

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Parse

theorem parse_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Routed s t 4)
    (size : bytes.size = 65) (rip : t.RIP = 0x110635) :
    ∃ fuel u, Advances boundary fuel t u ∧ Parsed s u bytes := by
  obtain ⟨ny,y,ry,sy⟩ := Parse.y_correct pre state size rip
  obtain ⟨nc,c,rc,fc,ic,raw,valid,_,gc⟩ := canonical_correct false pre sy.toFrameState
    size sy.rip sy.input (fun _ => ⟨sy.r15,sy.r12,sy.r13⟩)
  obtain ⟨nd,d,rd,fd,id,axd,vd,rbxd,_,r12d,_,r14d,_,kd⟩ :=
    x_converted pre fc ic raw valid
  obtain ⟨ne,e,re,fe,ie,ve,valide,abie,ke⟩ := x_selected pre fd id axd vd r12d
  obtain ⟨nf,u,rf,fu,iu,vu,ptr,abiu,ku⟩ := x_finished pre fe ie ve valide
  have bytesKept (off len : Nat) (pair : (off,len) ∈ [(312,32),(748,1)]) (i : Nat) (hi : i < len) :
      u.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
        y.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
    have bounds : off ≤ 760 ∧ len ≤ off+8 ∧ (off+32 ≤ 744 ∨ 744+len ≤ off) := by
      have cases : (off=312 ∧ len=32) ∨ (off=748 ∧ len=1) := by simpa using pair
      rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
    exact ((ku off len pair i hi).trans (ke off len pair i hi)).trans
      ((kd off len bounds.1 bounds.2.1 bounds.2.2 i hi).trans
        (coordinate_byte sy.toFrameState gc pair hi))
  refine ⟨ny+nc+nd+ne+nf,u,(((ry.trans rc).trans rd).trans re).trans rf,
    ⟨fu,iu,?_,ptr,?_,?_,?_,vu,?_⟩⟩
  · exact (((abiu .rbx (by simp)).trans (abie .rbx (by simp))).trans rbxd).trans
      ((gc.read (n := 64) (r := 3)
        (by simp [coordinateComponents,decodeComponents,storeComponents,Canonical.components])).trans sy.output)
  · exact (((abiu .r14 (by simp)).trans (abie .r14 (by simp))).trans r14d).trans
      ((gc.read (n := 64) (r := 14)
        (by simp [coordinateComponents,decodeComponents,storeComponents,Canonical.components])).trans sy.pointer)
  · exact (abiu .r15 (by simp)).trans valide
  · have h := bytesKept 748 1 (by simp) 0 (by decide)
    simp only [BitVec.add_zero] at h
    exact h.trans sy.valid
  · exact sy.value.of_bytes_eq (fun i hi => bytesKept 312 32 (by simp) i hi)

end P256.Proofs.Sec1.Affine.Uncompressed
