import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Sites
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1
def Site.prev : Site → Site
  | .roundFirst => .roundFirst
  | .mulFirst => .roundFirst
  | .roundSecond => .mulFirst
  | .mulSecond => .roundSecond
  | .addSecond => .mulSecond
  | .mulLambda => .addSecond
  | .addFirst => .mulLambda


set_option maxRecDepth 4096 in
set_option maxHeartbeats 950000 in
theorem callBlock (k : Site) (later : k ≠ .roundFirst)
    {fr : Activation} {p a : Registers} {m : Ram}
    (doneAt : k.prev.returned fr p a m) (widths : ParseSignature.ArgumentWidths a)
    (win : Writable Extracted.programImage m (sp fr - 8) 8) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨k.pc,a,m⟩ =
      .call ⟨k.callee,b,memStore m (sp fr - 8) k.ret⟩ (callFrame k.resume k.ret) ∧
      CallRegisters (k.child fr a) b := by
  obtain ⟨rs,df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := doneAt
  have rsp : a[4].get 64 = sp fr := by
    have eq := congrArg (Value.get 64) rs
    change a[4].get 64 = sp fr - 8 + 8 at eq
    simpa only [BitVec.sub_add_cancel] using eq
  have arg (i : Fin Reg.count) (h : i.val ∈ Activation.argumentNumbers) :
      a[i] = ⟨64,a[i].get 64⟩ := by
    have w := widths i h
    generalize a[i] = v at w ⊢
    cases v with | mk n x => cases w; rfl
  have cx := arg 1 (by decide)
  have r8 := arg 8 (by decide)
  have r9 := arg 9 (by decide)
  cases k <;> try exact False.elim (later rfl)
  case' mulFirst =>
    refine ⟨?_, ?run, ?_⟩
    case run =>
      dsimp only [Site.pc,Site.callee,Site.resume,Site.ret]
      arithmetic_segment using code_l11c95d [rsp]
  case' roundSecond =>
    refine ⟨?_, ?run, ?_⟩
    case run =>
      dsimp only [Site.pc,Site.callee,Site.resume,Site.ret]
      arithmetic_segment using code_l11c977 [rsp]
  case' mulSecond =>
    refine ⟨?_, ?run, ?_⟩
    case run =>
      dsimp only [Site.pc,Site.callee,Site.resume,Site.ret]
      arithmetic_segment using code_l11c989 [rsp]
  case' addSecond =>
    refine ⟨?_, ?run, ?_⟩
    case run =>
      dsimp only [Site.pc,Site.callee,Site.resume,Site.ret]
      arithmetic_segment using code_l11c9a3 [rsp]
  case' mulLambda =>
    refine ⟨?_, ?run, ?_⟩
    case run =>
      dsimp only [Site.pc,Site.callee,Site.resume,Site.ret]
      arithmetic_segment using code_l11c9c0 [rsp]
  case' addFirst =>
    refine ⟨?_, ?run, ?_⟩
    case run =>
      dsimp only [Site.pc,Site.callee,Site.resume,Site.ret]
      arithmetic_segment using code_l11c9d2 [rsp]
  all_goals
    refine ⟨rfl,df,?_,?_,?_,?_,?_,?_,r8,r9,?_,?_,?_,?_,mx,ft,fc⟩
  all_goals first
    | rfl | exact cx | exact bx | exact bp | exact r12 | exact r13 | exact r14 | exact r15
    | (apply congrArg (Value.mk 64); first
      | exact congrArg (Value.get 64) bx | exact congrArg (Value.get 64) bp
      | exact congrArg (Value.get 64) r12 | exact congrArg (Value.get 64) r13
      | exact congrArg (Value.get 64) r14 | exact congrArg (Value.get 64) r15)

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
