import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreStep
import P256.Proofs.Common.Instructions.CrossPageStore.Legacy

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem store_window [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t) (rip : t.RIP=0x11541a)
    (value : t.regValue .rax=16) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧ u.RIP=0x11541e ∧
      AgreesExcept [.mem (exponentFrameBase s+120#64) 4,.rip] t u ∧
      u.external=memStore t.external (exponentFrameBase s+120#64) (16#32) := by
  have sp : stackPtr t=exponentFrameBase s := hf.rsp
  have addr : storeAddrAt 0x11541a (.sib 4 none 0 (.d8 120)) 4 t=exponentFrameBase s+120#64 := by
    change stackPtr t+120#64=_
    rw [sp]
  have writable := ScalarFrame.stack_writable (frameOffset := 1416) ctx.toCalleePre hf
    (offset := 120) (len := 4) (by decide) (by decide) (by decide)
  rw [sp] at writable
  have apart := ScalarFrame.stack_code (frameOffset := 1416) ctx.toCalleePre hf
    (offset := 120) (len := 4) (codeOffset := 0x1541a) (codeLen := 4)
    (by decide) (by decide) (by decide)
  rw [sp] at apart
  obtain ⟨u,run,ready,effect⟩ := (mov_m32_r32_legacy_effect_step_any 0x11541a 0
      (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl).advances
    (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) 0x1541a _ (by decide) (by decide +kernel))
    ⟨rip,addr ▸ writable,addr ▸ apart⟩
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1541e (by decide)))
  have g : AgreesExcept [.mem (exponentFrameBase s+120#64) 4,.rip] t u := by
    have h := effect.agrees
    have len : 2+(AddrMode.sib 4 none 0 (.d8 120)).tail.length=4 := by decide
    simpa only [movM32R32LegacyEffect,storeEffect,Effect.components,Write.component,
      Operand.component,List.map_cons,List.map_nil,List.append_nil,List.cons_append,
      List.nil_append,len,addr] using h
  have stored : (Operand.mem (exponentFrameBase s+120#64) : Operand 32).read u=16 := by
    have h := effect.writes
    change (Operand.mem (storeAddrAt 0x11541a (.sib 4 none 0 (.d8 120)) 4 t) : Operand 32).read u=
      (t.regValue .rax).setWidth 32 at h
    rwa [addr,value] at h
  have frame := hf.after_effect (frameOffset := 1416) ctx.toCalleePre (by decide) ready g (by
    intro c hc a hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨ScalarFrame.workRegion s 1584,by simp,?_⟩
      have address : exponentFrameBase s+120#64=stackPtr s-1296#64 := by
        simp only [exponentFrameBase,stackPtr,BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      rw [address] at hv
      exact ScalarFrame.work_contains ctx.toCalleePre (by decide) (by decide) hv
    · exact hv.elim) (by simp)
  exact ⟨u,run,frame,effect.rip,g,P256.Proofs.Common.Field.SquareRoot.ExponentInitialize.external_of_store g writable.mem stored⟩

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
