import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Frame
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)

def prepareTagEffect (t : RamState) : Effect :=
  { rip := 0x111098
    writes := [⟨(.mem (rspOf t + 199) : Operand 8), (Operand.reg 0 : Operand 8).read t⟩] }

theorem prepare_tag [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) (rip : t.RIP = 0x111091) :
    ∃ u, FrameState s u 65 328 312 ∧ Advances boundary 1 t u ∧
      (prepareTagEffect t).Holds t u := by
  let am : AddrMode := .sib 4 none 0 (.d32 199)
  have haddr : storeAddrAt 0x111091 am 7 t = stackPtr s - 113 := by
    change stackPtr t + 199 = stackPtr s - 113
    exact scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 113) 1 :=
    writable_of_grow (stack_sub_writable pre.stack
      (fun a ha hr => pre.avoids _ (by simp) a ha (.inr hr))
      (by decide) (by decide) (by decide)
      (by have := Nat.mod_lt (stackPtr s - 113).toNat (by decide : 0 < 4096); omega))
      state.allocated
  have apart : RangeApart (stackPtr s - 113) 1 0x111091 7 := by
    have h := stack_code pre state (offset := 199) (len := 1)
      (codeOffset := 0x11091) (codeLen := 7) (by decide) (by decide) (by decide)
    rw [scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by decide)] at h
    exact h
  have code : CodeIn (codeRange 0x111091 [0x88,0x84,0x24,0xc7,0,0,0]) t :=
    programText_slice (programLoaded_codeIn state.loaded) 0x11091 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, run, ready, effect⟩ := (mov_m8_r8_legacy_effect_step 0x111091 0 (by decide)
    am (by simp [am, AddrMode.Valid]) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (by
      have hb : 0x88 :: am.modrm 0 :: am.tail = [0x88,0x84,0x24,0xc7,0,0,0] := by
        decide +kernel
      rw [hb]
      exact code)
    ⟨rip, haddr ▸ writable, haddr ▸ apart⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x11098 (by decide)))
  change (prepareTagEffect t).Holds t u at effect
  refine ⟨u, state_of_encoding pre state ready effect ?_ ?_, run, effect⟩
  · intro c hc
    simp only [prepareTagEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨199, rfl, by decide⟩
    · trivial
  · simp [prepareTagEffect, Effect.components, Write.component, Operand.component]

end P256.Proofs.Sec1Serialize.Prepare
