import Sha2.Proofs.Common.SHA256.Initialize.Contract
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Instructions.CrossPageStore.Compose
import Sha2.Proofs.Wrapper.Initialize.Store

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

@[local x86_compose] theorem Address.mode_addr (a : Address) (s : RamState) (instructionEnd : BitVec 64) :
    a.mode.addr s instructionEnd = a.read s := by
  unfold Address.mode
  split <;> rfl

@[local x86_compose] theorem Address.storeAddrAt (a : Address) (p : BitVec 64) (len : Nat) :
    storeAddrAt p a.mode len = a.read := by
  funext s
  exact a.mode_addr s _

theorem Address.read_eq {a : Address} {s t : RamState}
    (register : (.reg (a.base.setWidth 5) : Operand 64).read t =
      (.reg (a.base.setWidth 5) : Operand 64).read s) : a.read t = a.read s := by
  unfold Address.read
  rw [register]

theorem immediate_step [Bindings] (p : BitVec 64) (r : BitVec 4) (value : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeMovR64Imm64 r value))
      (movR64Imm64Effect p (r.setWidth 5) value) := by
  obtain ⟨rex, op, encoded, hpref, opcode, register⟩ := encodeMovR64Imm64_spec r value
  rw [encoded, ← register]
  exact mov_r64_imm64_effect_step p rex op hpref opcode value

theorem word_step [Bindings] (p : BitVec 64) (r : BitVec 4) (a : Address)
    (valid : a.mode.Valid) :
    StepEffect (CrossPageStore.Pre p (3 + a.mode.tail.length) a.read 8)
      (codeRange p (encodeMovM64R64 r a.mode))
      (movM64R64Effect p (r.setWidth 5) a.mode) := by
  obtain ⟨hpref, source, index, base⟩ := a.mode.rexByte_true_spec r
  have step := CrossPageStore.mov_m64_r64_effect_step_any p (a.mode.rexByte true r)
    hpref (regLow r) a.mode valid index base
  rw [source, gprNumber_reg] at step
  simpa only [encodeMovM64R64, Address.storeAddrAt] using step

theorem counter_step [Bindings] (p : BitVec 64) (a : Address) (valid : a.mode.Valid) :
    StepEffect (CrossPageStore.Pre p (7 + a.mode.tail.length) a.read 8)
      (codeRange p (encodeMovM64Imm32 a.mode 0))
      (movM64Imm32Effect p a.mode 0) := by
  obtain ⟨hpref, _, index, base⟩ := a.mode.rexByte_true_spec 0
  have step := CrossPageStore.mov_m64_imm32_effect_step_any p (a.mode.rexByte true 0)
    hpref a.mode valid index base 0
  simpa only [encodeMovM64Imm32, Address.storeAddrAt] using step

theorem tail_step [Bindings] (p : BitVec 64) (a : Address) (valid : a.mode.Valid)
    (index : a.mode.rexX = 0) (base : a.mode.rexB = 0) :
    StepEffect (StorePre p (3 + a.mode.tail.length) a.read 1)
      (codeRange p ([0xc6, a.mode.modrm 0] ++ a.mode.tail ++ [0]))
      (movM8Imm8Effect p a.mode 0) := by
  simpa only [Address.storeAddrAt, List.cons_append, List.nil_append,
    List.append_assoc, show immBytes 8 (0 : BitVec 8) = [0] from rfl] using mov_m8_imm8_effect_step p a.mode valid index base 0

end Sha2.Proofs.Common.SHA256.Initialize
