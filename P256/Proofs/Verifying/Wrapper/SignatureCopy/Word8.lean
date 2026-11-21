import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Memory
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy.Word8

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions.CrossPageStore

structure Pre (pc : BitVec 64) (source destination : BitVec 8) (s : RamState) : Prop where
  rip : s.RIP = pc
  readable : MemReadable s ((Operand.reg 4 : Operand 64).read s+source.signExtend 64) 8
  writable : Writable s ((Operand.reg 4 : Operand 64).read s+destination.signExtend 64) 8
  apart : RangeApart ((Operand.reg 4 : Operand 64).read s+destination.signExtend 64) 8 pc 10

def bytes (source destination : BitVec 8) : List UInt8 :=
  [0x48,0x8b,0x44,0x24,UInt8.ofBitVec source,0x48,0x89,0x44,0x24,UInt8.ofBitVec destination]

def effect (pc : BitVec 64) (source destination : BitVec 8) (s : RamState) : Effect :=
  let value := memLoad s.external ((Operand.reg 4 : Operand 64).read s+source.signExtend 64) 64
  { rip := pc+10
    writes := [⟨(.reg 0 : Operand 64),value⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+destination.signExtend 64) : Operand 64),value⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (pc : BitVec 64)
    (source destination : BitVec 8) (first : pc+5 ≠ boundary.rip) (last : pc+10 ≠ boundary.rip) :
    AdvancesBlock boundary (Pre pc source destination)
      (codeRange pc (bytes source destination)) (effect pc source destination) := by
  unfold bytes
  slice_run_begin (mov_r64_m64_effect_step pc 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 source)) ⟨by decide,fun h ↦ by cases h⟩ rfl rfl)
  case sub =>
    exact codeRange_mem_of_take (by simp [AddrMode.tail,AddrMode.modrm,AddrMode.mod,AddrMode.rm,
      Disp.mod,Disp.bytes,immBytes,immByte]; rfl)
  case boundary => intro _ _; exact first
  refine blockThen ?k (mov_m64_r64_effect_step_any (pc+5) 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 destination)) ⟨by decide,fun h ↦ by cases h⟩ rfl rfl) (by x86_local) ?sub (by x86_full) ?mid ?next
  case sub =>
    exact codeRange_mem_of_drop (p := pc) 5 (by simp [AddrMode.tail,AddrMode.modrm,AddrMode.mod,
      AddrMode.rm,Disp.mod,Disp.bytes,immBytes,immByte]; rfl)
  case mid =>
    intro s t hp he ho
    refine ⟨storePre_of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_⟩
    · x86_norm; exact hp.writable
    · x86_norm; exact hp.apart.sub 5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      exact Effect.avoids_of_components_mem_rip (a := (Operand.reg 4 : Operand 64).read s+destination.signExtend 64) (len := 8) (by x86_norm [Effect.components]) (by x86_norm; exact hp.apart)
  case next => intro _ _; simpa only [movM64R64Effect,storeEffect,AddrMode.tail,Disp.bytes,immBytes_length,
      List.length_cons,Nat.reduceDiv,Nat.reduceAdd,BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using last
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [effect]
  · x86_norm [effect]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Wrapper.SignatureCopy.Word8
