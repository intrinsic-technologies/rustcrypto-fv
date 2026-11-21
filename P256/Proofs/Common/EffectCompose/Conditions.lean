import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov
import P256.Proofs.Common.Instructions.CmovMemory.Effect

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR32M32Effect cmovR32M32Value cmovR32R32Effect cmovR32R32Value cmovR64R64Effect cmovR64R64Value)
open P256.Proofs.Common.Instructions.Setb (setccM8Effect setccR8Effect setccValue)
open X86Proofs

namespace P256.Proofs.Common.EffectCompose

open X86 X86.Machine X86.UserProcess

@[x86_local_on] theorem cmovR64R64Effect_localOn_cf (p : BitVec 64) (dst src : BitVec 5) {cc : BitVec 4} (hcc : cc = 2) :
    Effect.LocalOn [.CF] (cmovR64R64Effect p cc dst src) := by
  subst cc
  apply Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).CF := hf .CF (by simp)
    simp [cmovR64R64Effect, cmovR64R64Value, condHolds, ho.read_reg, hc]
  · intro t
    simp [cmovR64R64Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem cmovR64R64Effect_localOn_ne (p : BitVec 64) (dst src : BitVec 5) {cc : BitVec 4} (hcc : cc = 5) :
    Effect.LocalOn [.ZF] (cmovR64R64Effect p cc dst src) := by
  subst cc
  apply Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).ZF := hf .ZF (by simp)
    simp [cmovR64R64Effect, cmovR64R64Value, condHolds, ho.read_reg, hc]
  · intro t
    simp [cmovR64R64Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem cmovR32R32Effect_localOn_cf (p : BitVec 64) (dst src : BitVec 5) {cc : BitVec 4} (hcc : cc = 2) :
    Effect.LocalOn [.CF] (cmovR32R32Effect p cc dst src) := by
  subst cc
  apply Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).CF := hf .CF (by simp)
    simp [cmovR32R32Effect, cmovR32R32Value, condHolds, ho.read_reg, hc]
  · intro t
    simp [cmovR32R32Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem setccR8Effect_localOn_cf (p : BitVec 64) (len : Nat) (dst : BitVec 5) {cc : BitVec 4} (hcc : cc = 2) :
    Effect.LocalOn [.CF] (setccR8Effect p len dst cc) := by
  subst cc
  apply Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).CF := hf .CF (by simp)
    simp [setccR8Effect, setccValue, condHolds, ho.gpr, hc]
  · intro t
    simp [setccR8Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem setccR8Effect_localOn_zf (p : BitVec 64) (len : Nat) (dst : BitVec 5) {cc : BitVec 4} (hcc : cc = 4) :
    Effect.LocalOn [.ZF] (setccR8Effect p len dst cc) := by
  subst cc
  apply Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).ZF := hf .ZF (by simp)
    simp [setccR8Effect, setccValue, condHolds, ho.gpr, hc]
  · intro t
    simp [setccR8Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem setccM8Effect_localOn_cf
    (p : BitVec 64) (len : Nat) (am : AddrMode) {cc : BitVec 4} (hcc : cc = 2) :
    Effect.LocalOn [.CF] (setccM8Effect p len am cc) := by
  subst cc
  apply Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).CF := hf .CF (by simp)
    simp [setccM8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs ho, setccValue, condHolds, hc]
  · intro t
    simp [setccM8Effect, storeEffect, Write.Full, Operand.Full]

attribute [x86_compose] cmovR64R64Effect cmovR64R64Value cmovR32R32Effect cmovR32R32Value
  setccR8Effect setccM8Effect setccValue condHolds cmovR32M32Effect cmovR32M32Value

end P256.Proofs.Common.EffectCompose
