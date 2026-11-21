import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import Sha2.Proofs.Common.Instructions.ForgetFlags
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine.Epilogue

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

inductive Layout where
  | five272
  | six200
  | six312
  | six552
  | six376
  | six584
  | six600

def Layout.allocation : Layout → Nat
  | .five272 => 272
  | .six200 => 200
  | .six312 => 312
  | .six552 => 552
  | .six376 => 376
  | .six584 => 584
  | .six600 => 600

def Layout.six : Layout → Bool
  | .five272 => false
  | .six200 | .six312 | .six552 | .six376 | .six584 | .six600 => true

def Layout.length (layout : Layout) : Nat := if layout.six then 17 else 16

def bytes (layout : Layout) : List UInt8 :=
  [0x48, 0x81, 0xc4] ++ immBytes 32 (BitVec.ofNat 32 layout.allocation) ++
    [0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f] ++
    (if layout.six then [0x5d] else [])

structure Pre (p : BitVec 64) (layout : Layout) (s : RamState) : Prop where
  rip : s.RIP = p
  read0 : MemReadable s (rspOf s + BitVec.ofNat 64 layout.allocation) 8
  read1 : MemReadable s (rspOf s + BitVec.ofNat 64 (layout.allocation + 8)) 8
  read2 : MemReadable s (rspOf s + BitVec.ofNat 64 (layout.allocation + 16)) 8
  read3 : MemReadable s (rspOf s + BitVec.ofNat 64 (layout.allocation + 24)) 8
  read4 : MemReadable s (rspOf s + BitVec.ofNat 64 (layout.allocation + 32)) 8
  read5 : if layout.six then
    MemReadable s (rspOf s + BitVec.ofNat 64 (layout.allocation + 40)) 8 else True

def effect (p : BitVec 64) (layout : Layout) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 layout.length
    writes := [
      ⟨(.reg 3 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 layout.allocation) 64⟩,
      ⟨(.reg 12 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 8)) 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 16)) 64⟩,
      ⟨(.reg 14 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 24)) 64⟩,
      ⟨(.reg 15 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 32)) 64⟩] ++
      (if layout.six then [⟨(.reg 5 : Operand 64),
        memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 40)) 64⟩] else []) ++
      [⟨(.reg 4 : Operand 64), rspOf s + BitVec.ofNat 64
        (layout.allocation + if layout.six then 48 else 40)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

attribute [local x86_compose] Layout.allocation Layout.six Layout.length

macro "sha256_restore_steps " allocation:num "," count:num "," pc:term "," outside:term "," inside:term : tactic => do
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  steps := steps.push (← `(tactic| advance_reloc_begin
    (StepEffect.forgetFlags (h :=
      (show StepEffect _ _ (addR64Imm32Effect $pc 4 $allocation) from
        add_r64_imm32_effect_step $pc 0x48 0xc4 $allocation
          (by constructor <;> decide) (by decide) (by decide))))
    next (boundary_ne_program $outside ($inside 7 (by decide)))))
  let registers := if count.getNat = 6 then [3,12,13,14,15,5] else [3,12,13,14,15]
  let mut pos := 7
  for r in registers do
    let pcNow ← `($pc + $(Lean.quote pos))
    pos := pos + (if r < 8 then 1 else 2)
    steps := steps.push (← `(tactic| advance_reloc_then
      (Common.Encoding.Serialize.pop_register_effect_step $pcNow $(Lean.quote r) (by decide))
      next (boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))))
  let mut result ← `(tactic| advance_finish [effect, Layout.allocation, Layout.six, Layout.length])
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

set_option maxHeartbeats 600000 in
theorem restore [Bindings] (p : BitVec 64) (layout : Layout) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p layout.length) :
    AdvanceTriple boundary (Pre p layout) (codeRange p (bytes layout))
      (Effect.post (effect p layout)) := by
  cases layout with
  | five272 => sha256_restore_steps 272, 5, p, outside, inside
  | six200 => sha256_restore_steps 200, 6, p, outside, inside
  | six312 => sha256_restore_steps 312, 6, p, outside, inside
  | six552 => sha256_restore_steps 552, 6, p, outside, inside
  | six376 => sha256_restore_steps 376, 6, p, outside, inside
  | six584 => sha256_restore_steps 584, 6, p, outside, inside
  | six600 => sha256_restore_steps 600, 6, p, outside, inside

theorem bytes_length (layout : Layout) : (bytes layout).length = layout.length := by
  cases layout <;> decide +kernel

theorem finish [Bindings] (p : BitVec 64) (layout : Layout) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p layout.length)
    (s : RamState) (ready : ReadyToStep s)
    (loaded : CodeIn (codeRange p (bytes layout ++ [0xc3])) s)
    (pre : Pre p layout s)
    (readable : MemReadable s (rspOf s + BitVec.ofNat 64
      (layout.allocation + if layout.six then 48 else 40)) 8)
    (returnWord : memLoad s.external (rspOf s + BitVec.ofNat 64
      (layout.allocation + if layout.six then 48 else 40)) 64 = boundary.rip)
    (returnStack : rspOf s + BitVec.ofNat 64
      (layout.allocation + if layout.six then 48 else 40) + 8 = boundary.rsp)
    (low : boundary.rip.toNat < 2^32) :
    ∃ fuel t u, Returns boundary fuel s t ∧ ReadyToStep t ∧
      (effect p layout s).Holds s u ∧ (retEffect u).Holds u t ∧ t.external = s.external := by
  have first : CodeIn (codeRange p (bytes layout)) s := loaded.mono (by
    intro x hx
    rw [codeRange_append]
    exact List.mem_append_left _ hx)
  have last : CodeIn (codeRange (p + BitVec.ofNat 64 layout.length) [0xc3]) s := loaded.mono (by
    intro x hx
    rw [codeRange_append, bytes_length]
    exact List.mem_append_right _ hx)
  obtain ⟨fuel, u, run, readyU, _, result⟩ := restore p layout boundary outside inside s ready first pre
  have memory : u.external = s.external := result.agrees.external (by
    cases layout <;> simp [effect, Layout.six, Effect.components, Write.component,
      Operand.component, Component.Covers])
  have rsp : stackPtr u = rspOf s + BitVec.ofNat 64
      (layout.allocation + if layout.six then 48 else 40) := by
    have hw := Write.allHold_iff.mp result.writes
      (⟨(.reg 4 : Operand 64), rspOf s + BitVec.ofNat 64
        (layout.allocation + if layout.six then 48 else 40)⟩ : Write)
      (by simp [effect])
    exact hw
  have lastU : CodeIn (codeRange (p + BitVec.ofNat 64 layout.length) [0xc3]) u := by
    apply result.codeIn _ last
    apply Effect.Avoids.of_noMem
    cases layout <;> simp [effect, Layout.six, Effect.components, Write.component,
      Operand.component, Component.Covers]
  have top : stackTop u = boundary.rip := by
    change memLoad u.external (stackPtr u) 64 = boundary.rip
    rw [rsp, memory, returnWord]
  obtain ⟨t, step, readyT, resultT⟩ := ret_effect_step (p + BitVec.ofNat 64 layout.length)
    u readyU lastU ⟨⟨result.rip, by rw [rsp]; exact readable.of_holds result⟩, top ▸ low⟩
  have returns : Returns boundary 1 u t := Returns.of_step step
    (resultT.rip.trans top) (by
      change stackPtr t = boundary.rsp
      have hw : stackPtr t = stackPtr u + 8 := resultT.writes
      rw [hw, rsp, returnStack])
  refine ⟨fuel + 1, t, u, run.returns returns, readyT, result, resultT, ?_⟩
  rw [resultT.agrees.external (by simp [Component.Covers]), memory]

end Sha2.Proofs.Common.Machine.Epilogue
