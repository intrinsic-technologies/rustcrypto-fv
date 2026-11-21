import Base16ct.Proofs.Copied.P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace Base16ct.Proofs.EncodeStr.Lower

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def movM8R8Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (storeAddrAt p am len) fun s ↦ (Operand.reg src : Operand 8).read s

attribute [x86_compose] movM8R8Effect

@[x86_local] theorem movM8R8Effect_local (p : BitVec 64) (len : Nat)
    (src : BitVec 5) (am : AddrMode) : Effect.Local (movM8R8Effect p len src am) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movM8R8Effect, storeEffect, AddrMode.addr_obs h]
  · simp [movM8R8Effect, storeEffect, h.read_reg, AddrMode.addr_obs h]
  · simpa only [movM8R8Effect, storeEffect, Effect.flag] using congrArg some hi
  · simp [movM8R8Effect, storeEffect, Write.Full, Operand.Full]

theorem mov_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post
        (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect
    (fun _ hpre ↦ storeEffect_avoids (by simp only [List.length_cons]; omega) _ _ hpre)
    (Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.mov_m8_r8_effect_step p rex hrex reg am hv hx hb)

theorem store_high_effect_step [Bindings] :
    StepEffect (StorePre 0x1004f4 4 (storeAddrAt 0x1004f4 (.sib 1 (some 8) 1 .none) 4) 1)
      (codeRange 0x1004f4 [0x46, 0x88, 0x1c, 0x41])
      (movM8R8Effect 0x1004f4 4 11 (.sib 1 (some 8) 1 .none)) :=
  Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x1004f4 0x46
    (by unfold RexPrefix; decide +kernel) 3 (.sib 1 (some 8) 1 .none) (by decide +kernel) rfl rfl

theorem store_low_effect_step [Bindings] :
    StepEffect (StorePre 0x100514 5 (storeAddrAt 0x100514 (.sib 1 (some 8) 1 (.d8 1)) 5) 1)
      (codeRange 0x100514 [0x46, 0x88, 0x54, 0x41, 0x01])
      (movM8R8Effect 0x100514 5 10 (.sib 1 (some 8) 1 (.d8 1))) :=
  Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x100514 0x46
    (by unfold RexPrefix; decide +kernel) 2 (.sib 1 (some 8) 1 (.d8 1)) (by decide +kernel) rfl rfl

theorem store_high_triple [Bindings] :
    Triple (StorePre 0x1004f4 4 (storeAddrAt 0x1004f4 (.sib 1 (some 8) 1 .none) 4) 1)
      (codeRange 0x1004f4 [0x46, 0x88, 0x1c, 0x41])
      (Effect.post (movM8R8Effect 0x1004f4 4 11 (.sib 1 (some 8) 1 .none))) :=
  mov_m8_r8_triple_of_bytes 0x1004f4 0x46 (by unfold RexPrefix; decide +kernel) 3
    (.sib 1 (some 8) 1 .none) (by decide +kernel) rfl rfl

theorem store_low_triple [Bindings] :
    Triple (StorePre 0x100514 5 (storeAddrAt 0x100514 (.sib 1 (some 8) 1 (.d8 1)) 5) 1)
      (codeRange 0x100514 [0x46, 0x88, 0x54, 0x41, 0x01])
      (Effect.post (movM8R8Effect 0x100514 5 10 (.sib 1 (some 8) 1 (.d8 1)))) :=
  mov_m8_r8_triple_of_bytes 0x100514 0x46 (by unfold RexPrefix; decide +kernel) 2
    (.sib 1 (some 8) 1 (.d8 1)) (by decide +kernel) rfl rfl

theorem movM8R8Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (movM8R8Effect p len src am s).components = [.mem (storeAddrAt p am len s) 1, .rip] := by
  simp [movM8R8Effect]

end Base16ct.Proofs.EncodeStr.Lower
