import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Start.Entry
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Composition.Generator

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Start

theorem generatorInput {fr : Activation} {initial : Registers} {d : Nat} {q : Ram}
    (e : CoreEntry fr initial d) (frame : RamWriteFrame fr.original q [fr.region])
    (loaded : ∀ x ∈ Extracted.programImage, q[x.1]? = some x.2) :
    ∀ i : Fin 15, memLoad q (wordAddr fr.rsi 64 i.val) 64 =
      memLoad q (wordAddr 0x202bc8 64 i.val) 64 := by
  have original := Endomorphism.sourceWords e.loaded e.generator
  have input := WordsAt.of_frame original frame (by decide) (generatorOutside e)
  have constant := Endomorphism.sourceWords loaded (src := 0x202bc8) (fun _ => rfl)
  exact fun i => (input i.val i.isLt).trans (constant i.val i.isLt).symm

structure Returned (fr : Activation) (b : Registers) (m : Ram) (d : Nat)
    (out : Output Value Ram Reg.count) : Prop where
  run : program.Exec (dialect Extracted.programImage) ⟨⟨.l10e010,b,memory fr m d⟩,[]⟩ out
  tag : out.tag = some ⟨64,0x11ca7f⟩
  done_ : Atom.All Extracted.programImage out.values out.store (Fn10e010.doneAt (callee fr b m d))
  widths : ParseSignature.ArgumentWidths out.values
  frame : RamWriteFrame (memory fr m d) out.store
    [⟨(sp fr - 8).toNat - 128,128⟩,⟨(sp fr + 0x2b0).toNat,120⟩]
  endo : endoAt fr out.store

set_option maxRecDepth 2048 in
theorem call {fr : Activation} {initial b : Registers} {m : Ram} {d : Nat}
    (e : CoreEntry fr initial d) (frame : RamWriteFrame fr.original (memory fr m d) [fr.region])
    (args : Arguments fr b d)
    (entry : Atom.All Extracted.programImage b (memory fr m d) (Fn10e010.frameAt .l10e010 (callee fr b m d))) :
    ∃ out, Returned fr b m d out := by
  let c := callee fr b m d
  have csi : c.rsi = fr.rsi := congrArg (Value.get 64) args.rsi
  have cdi : c.rdi = sp fr + 0x2b0 := congrArg (Value.get 64) args.rdi
  have csp : c.rsp = sp fr - 8 := rfl
  have loaded := e.loaded_of_frame (coreFrame frame)
  have memEq := generatorInput e frame loaded
  have src := e.pairRead.of_frame frame
  have read : Readable (memory fr m d) fr.rsi 120 := src.sub (Nat.le_refl _) (by omega)
  have dst := Split.Caller.slotWrite e (Split.Caller.stackAccess e frame) (i := 0x2b0) (n := 120) (by decide)
  have := e.room
  have high := e.high
  have top := Split.Caller.spNat e
  change (sp fr).toNat = fr.rsp.toNat - 3256 at top
  have push := Split.Caller.pushNat e
  change (sp fr - 8).toNat = (sp fr).toNat - 8 at push
  have off : (sp fr + 0x2b0).toNat = (sp fr).toNat + 0x2b0 := Split.Caller.slotNat e 0x2b0 (by decide)
  have pair : fr.rsi.toNat = fr.rsp.toNat + 0xf10 := by rw [e.pairPtr]; bv_omega
  obtain ⟨out,run,tag,done_,widths,foot,endo⟩ := endomorphismCall (fr := c) entry loaded
    (csi.symm ▸ read) (cdi.symm ▸ dst) (by rw [csp,csi]; omega) (by rw [csp,cdi]; omega)
    (Or.inr (by rw [cdi,csi]; omega)) (csi.symm ▸ memEq)
  rw [csp,cdi] at foot
  rw [cdi] at endo
  exact ⟨out,run,tag,done_,widths,foot,endo⟩

end Start

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
