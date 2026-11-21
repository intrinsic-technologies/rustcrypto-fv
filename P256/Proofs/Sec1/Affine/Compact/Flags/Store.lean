import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Flags

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive StoreSite
  | original
  | negative
  | minimum

def StoreSite.pc : StoreSite → BitVec 64
  | .original => 0x110310
  | .negative => 0x1103b0
  | .minimum => 0x110540

def StoreSite.offset : StoreSite → Nat
  | .original => 160
  | .negative => 232
  | .minimum => 704

def StoreSite.bytes (site : StoreSite) : List UInt8 :=
  [0x44,0x88,0xb4,0x24] ++ immBytes 32 (BitVec.ofNat 32 site.offset)

def StoreSite.effect (site : StoreSite) (s : RamState) : Effect :=
  { rip := site.pc + 8
    writes := [⟨(.mem (stackPtr s + BitVec.ofNat 64 site.offset) : Operand 8),
      (s.regValue .r14).setWidth 8⟩] }

theorem store_step [Bindings] (site : StoreSite) :
    StepEffect (StorePre site.pc 8 (fun s => stackPtr s + BitVec.ofNat 64 site.offset) 1)
      (codeRange site.pc site.bytes) site.effect := by
  cases site with
  | original =>
    exact P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x110310 0x44 (by simp [RexPrefix])
      6 (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl
  | negative =>
    exact P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x1103b0 0x44 (by simp [RexPrefix])
      6 (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl
  | minimum =>
    exact P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x110540 0x44 (by simp [RexPrefix])
      6 (.sib 4 none 0 (.d32 704)) (by decide) rfl rfl


theorem store_flag [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t) (site : StoreSite)
    (rip : t.RIP = site.pc) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧ u.RIP = site.pc + (8 : BitVec 64) ∧
      memLoad u.external (stackPtr s - BitVec.ofNat 64 (760-site.offset)) 8 =
        (t.regValue .r14).setWidth 8 ∧
      AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 (760-site.offset)) 1, .rip] t u := by
  have bound : site.offset + 1 ≤ 712 := by cases site <;> decide
  have codeBound : site.pc.toNat - 0x100000 + 8 ≤ 118431 := by cases site <;> decide
  have codeAddress : Extracted.textAddress + BitVec.ofNat 64 (site.pc.toNat - 0x100000) = site.pc := by
    cases site <;> decide
  have code := programText_slice (programLoaded_codeIn state.loaded)
    (site.pc.toNat-0x100000) site.bytes codeBound (by cases site <;> decide +kernel)
  rw [codeAddress] at code
  have writable := ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state
    (offset := site.offset) (len := 1) (by decide) (by omega) (by decide)
  have address : stackPtr t + BitVec.ofNat 64 site.offset =
      stackPtr s - BitVec.ofNat 64 (760-site.offset) :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by omega)
  obtain ⟨u,run,ready,effect⟩ := (store_step site).advances
    (readyToStep state.machine state.bindingsSupported) code
    ⟨rip, ⟨writable.low, writable.mem, writable.tables⟩, by
      have h := ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state
        (offset := site.offset) (len := 1) (by decide) (by omega) codeBound
      rwa [codeAddress] at h⟩
    (boundary_ne_program pre.outerBoundary (by
      cases site
      · exact inProgram_of_textOffset 0x10318 (by decide)
      · exact inProgram_of_textOffset 0x103b8 (by decide)
      · exact inProgram_of_textOffset 0x10548 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 (760-site.offset)) 1, .rip] t u := by
    have h := effect.agrees
    simp only [StoreSite.effect,Effect.components,List.map_cons,List.map_nil,Write.component,
      Operand.component,Nat.reduceDiv,List.append_nil] at h
    rwa [address] at h
  have frame : Frame s u := by
    apply state.after_effect pre.toCalleePre (by decide) ready agrees
    · intro c hc a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨ScalarFrame.workRegion s 3360,by simp,
          ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha⟩
      · exact ha.elim
    all_goals simp
  refine ⟨u,run,frame,effect.rip,?_,agrees⟩
  have value : memLoad u.external (stackPtr t + BitVec.ofNat 64 site.offset) 8 =
      (t.regValue .r14).setWidth 8 := effect.writes
  rwa [address] at value

end P256.Proofs.Sec1.Affine.Compact.Flags
