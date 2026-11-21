import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Converted
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Selected
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.YFinished

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ParsedY [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110820
  output : t.regValue .rbx = s.regValue .rdi
  input : t.regValue .rbp = s.regValue .rsi
  r12 : t.regValue .r12 = 0xffffffff
  r13 : t.regValue .r13 = 0
  r15 : t.regValue .r15 = 0xffffffff00000001
  pointer : t.regValue .r14 = stackPtr s-312
  valid : t.external[stackPtr s-748]? = some (if yCoordinate bytes < Operations.domain.p then 1 else 0)
  value : Field.MontgomeryAt t (stackPtr s-312) (canonical (yCoordinate bytes))

theorem y_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Routed s t 4)
    (size : bytes.size = 65) (rip : t.RIP = 0x110635) :
    ∃ fuel u, Advances boundary fuel t u ∧ ParsedY s u bytes := by
  obtain ⟨nc,c,rc,fc,ic,raw,valid,constants,gc⟩ := canonical_correct true pre state.toFrameState
    size rip state.input (by intro h; cases h)
  obtain ⟨nd,d,rd,fd,id,axd,vd,rbxd,rbpd,r12d,r13d,r14d,r15d,_⟩ :=
    y_converted pre fc ic raw valid
  obtain ⟨ne,e,re,fe,ie,ve,valide,abie,_⟩ := y_selected pre fd id axd vd
  obtain ⟨nf,u,rf,fu,iu,vu,ptr,abiu,tag⟩ := y_finished pre fe ie ve valide
  have keep (r : Syntax.Reg)
      (hr : r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r15]) : u.regValue r = d.regValue r :=
    (abiu r hr).trans (abie r hr)
  refine ⟨nc+nd+ne+nf,u,((rc.trans rd).trans re).trans rf,
    ⟨fu,iu,?_,?_,?_,?_,?_,ptr,tag,vu⟩⟩
  · exact ((keep .rbx (by simp)).trans rbxd).trans
      ((gc.read (n := 64) (r := 3)
        (by simp [coordinateComponents,decodeComponents,storeComponents,Canonical.components])).trans state.output)
  · exact ((keep .rbp (by simp)).trans rbpd).trans
      ((gc.read (n := 64) (r := 6)
        (by simp [coordinateComponents,decodeComponents,storeComponents,Canonical.components])).trans state.input)
  · exact ((keep .r12 (by simp)).trans r12d).trans (constants rfl).2.1
  · exact ((keep .r13 (by simp)).trans r13d).trans (constants rfl).2.2
  · exact ((keep .r15 (by simp)).trans r15d).trans (constants rfl).1

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
