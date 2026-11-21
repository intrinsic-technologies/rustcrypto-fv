import K256.Proofs.ParseSignature.Contract
import K256.Proofs.ParseSignature.Call
import K256.Proofs.LIR.Fn103ac0.Frame
import K256.Proofs.LIR.Fn107730.Frame
import K256.Spec.Ecdsa

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

abbrev sp (fr : Activation) := fr.rsp - 184

abbrev reaches (code : CodeMap) (l : Label) (args : Values Value Reg.count) (mem : Ram)
    (l' : Label) (args' : Values Value Reg.count) (mem' : Ram) :=
  (program.sem (dialect code)).Reaches ⟨⟨l, args, mem⟩, []⟩ ⟨⟨l', args', mem'⟩, []⟩

structure Active (code : CodeMap) (fr : Activation) (slots : Bool)
    (args : Values Value Reg.count) (mem : Ram) : Prop where
  atoms : Atom.All code args mem (Fn103ac0.frameAt (if slots then .l103b07 else .l103b80) fr)
  writes : RamWriteFrame fr.original mem [fr.region]
  widths : ArgumentWidths args

abbrev scalarChild (fr : Activation) (ret : BitVec 64) (args : Values Value Reg.count)
    (mem : Ram) : Activation :=
  { fr with original := mem, rsp := fr.rsp - 192, low := fr.rsp - 560, ret := ret,
            rbx := fr.rdi, r14 := fr.rsi, rdi := sp fr + 8, rsi := sp fr + 72, rdx := 32,
            rcx := args[1].get 64, r8 := args[8].get 64, r9 := args[9].get 64 }

def resumeAt (l : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨l, #v[], rfl, some ⟨64, ret⟩⟩

theorem reachesOfCall {code : CodeMap} {start callee finish : Label} {ret : BitVec 64}
    {args regs : Values Value Reg.count} {mem pushed : Ram} {out : Output Value Ram Reg.count}
    (call : program.runBlock (dialect code) ⟨start, args, mem⟩ =
      .call ⟨callee, regs, pushed⟩ (resumeAt finish ret))
    (exec : program.Exec (dialect code) ⟨⟨callee, regs, pushed⟩, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) :
    reaches code start args mem finish out.values out.store := by
  let frame := resumeAt finish ret
  have accepts : frame.Accepts (dialect code) out.tag = true := by
    rw [tag]
    change decide (Value.mk 64 ret = Value.mk 64 ret) = true
    exact decide_eq_true rfl
  refine .step (b := ⟨⟨callee, regs, pushed⟩, [frame]⟩) ?_ ?_
  · change (program.runBlock (dialect code) _).next _ [] = _
    rw [call]
    rfl
  · have back := exec_reaches_resume exec frame [] accepts
    have sameArgs := resume_arguments frame out
    dsimp only [StackFrame.resume] at sameArgs
    simp only [List.nil_append, StackFrame.resume, sameArgs] at back
    exact back

theorem stackSub_toNat {fr : Activation} (room : fr.low.toNat + 560 ≤ fr.rsp.toNat) (off : Nat) (ho : off ≤ 560) :
    (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
  have h : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h]; omega), h]

structure ScalarEntry (code : CodeMap) (fr : Activation) (ret src : BitVec 64)
    (args : Values Value Reg.count) (mem : Ram) : Prop where
  atoms : Atom.All code args mem (Fn107730.frameInfo.entryAtoms (scalarChild fr ret args mem))
  caller : ∃ regs, Atom.All code regs mem (Fn103ac0.frameAt .l103b07 fr)
  writes : RamWriteFrame fr.original mem [fr.region]
  words : ∀ i < 4, scalarWord mem (sp fr + 72) i = scalarWord fr.original src i

end K256.Proofs.ParseSignature.Pair
