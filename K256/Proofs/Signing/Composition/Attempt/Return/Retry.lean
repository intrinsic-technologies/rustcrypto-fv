import K256.Proofs.Signing.Composition.Attempt.Return.State
import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Return

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

private theorem retryBlocks {s : RamState} {code : CodeMap} {a : Registers} {m : Ram}
    (regs : RegistersAt s a (sp s+456) (sp s+192) (sp s+192) (sp s+456))
    (h8 : LoadOk m (sp s+8) 1) (h16 : LoadOk m (sp s+16) 8) (h24 : LoadOk m (sp s+24) 8)
    (tag : memLoad m (sp s+8) 8 = 1) (nilPtr : memLoad m (sp s+16) 64 = 0) :
    ∃ b c e : Registers,
      LIR.program.runBlock (dialect code) ⟨.l105d35,a,m⟩ = .jump ⟨.l105d46,b,m⟩ ∧
      LIR.program.runBlock (dialect code) ⟨.l105d46,b,m⟩ = .jump ⟨.l105870,c,m⟩ ∧
      LIR.program.runBlock (dialect code) ⟨.l105870,c,m⟩ = .jump ⟨.l105886,e,m⟩ ∧
      Nonce.CandidateRegisters e (sp s) ∧ e[39].width = 32 ∧ e[50].width = 16 ∧ e[51].width = 16 := by
  have rsp := congrArg (Value.get 64) regs.rsp
  change a[4].get 64 = sp s at rsp
  refine ⟨?_,?_,?_,?first,?next,?back,?post⟩
  case first =>
    cfg_eval [rsp,h8,h16,h24,tag,nilPtr]
    rfl
  case next =>
    cfg_eval
    rfl
  case back =>
    cfg_eval [rsp]
    rfl
  case post =>
    refine ⟨⟨regs.rsp,regs.df,regs.rbx,?_,regs.r12,?_,regs.r14,?_,?_⟩,regs.fp⟩
    · exact congrArg (fun v => Value.mk 64 (v.get 64)) regs.r13
    · rfl
    · rfl
    · intro i hi
      rcases i with ⟨i,hi'⟩
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
      · rfl
      · exact regs.widths 6 (by decide)
      · exact regs.widths 2 (by decide)
      · exact regs.widths 1 (by decide)
      · exact regs.widths 8 (by decide)
      · exact regs.widths 9 (by decide)

theorem retry {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {r sigS : Nat}
    (input : Constructed s d msg st r sigS a m) (zero : r = 0 ∨ sigS = 0) :
    ∃ b n, Reach (core .l105d35 a m) (core .l105886 b n) ∧ Outer s d msg st b n := by
  have win := (input.toMemory.window call).readable
  have base : stackPtr s - 11192 = sp s + (-9904) := by unfold sp; bv_omega
  have out := input.output
  rw [ite_eq_left zero] at out
  obtain ⟨tag,ptr⟩ := out
  obtain ⟨b,c,e,p,q,v,regs,fp⟩ := retryBlocks (code := Extracted.programImage) input.toRegistersAt
    (LoadOk.of_offsets win rfl base (by decide))
    (LoadOk.of_offsets win rfl base (by decide))
    (LoadOk.of_offsets win rfl base (by decide))
    tag ptr
  refine ⟨e,m,.step (b := core .l105d46 b m) ?_ (.step (b := core .l105870 c m) ?_
    (.step ?_ (.refl _))),input.toCoreMemory,regs,fp,input.hash,input.order,input.orderPtr,input.state⟩
  · exact congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) p
  · exact congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) q
  · exact congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) v

end K256.Proofs.Signing.Composition.Attempt.Return
