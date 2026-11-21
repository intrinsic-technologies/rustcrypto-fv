import P256.Proofs.Projective.Multiply.Machine.Radix.CopyArguments
import P256.Proofs.Projective.Multiply.Machine.Radix.CopyCall
import P256.Proofs.Projective.Multiply.Machine.Radix.Digits

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem digits_bytes [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : DigitsState s t d) :
    Bytes t.external (stackPtr s-112) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)) := by
  have readable : MemReadable t (stackPtr s-112) 65 := by
    have h := state.toState.stack_readable (frameOffset := 120) (offset := 8)
      (len := 65) pre (by decide) (by decide)
    rw [state.rsp] at h
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using h
  have raw := Bytes.of_isSome readable.mem
  apply raw.congr
  intro i hi
  apply UInt8.eq_of_toBitVec_eq
  exact (raw.loadByte i hi).symm.trans (state.digits i hi)

theorem copy_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : DigitsState s t d)
    (output : t.regValue .rbx = s.regValue .rdi) :
    ∃ u fuel, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x10ba7f ∧
      u.regValue .rbx = s.regValue .rdi ∧
      Bytes u.external (s.regValue .rdi) 65
        (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)) := by
  obtain ⟨n,v,run,ready,_,effect⟩ := copy_arguments boundary pre.outerBoundary t state.ready
    (programText_slice (programLoaded_codeIn (state.toState.loaded pre)) 0xba6c copyArgumentsBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [copyArgumentsEffect,Effect.components,Component.Covers])
  have frame : State s v := state.toState.after_registers pre ready effect.agrees
    (by simp [copyArgumentsEffect,Effect.components,registers])
    (by simp [copyArgumentsEffect,Effect.components,Component.Covers])
    ((effect.agrees.read (n := 64) (r := 4)
      (by simp [copyArgumentsEffect,Effect.components])).trans state.rsp)
  have source : v.regValue .rsi = stackPtr s-112 := by
    have h : v.regValue .rsi = stackPtr t+8 := effect.writes.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have dest : v.regValue .rdi = s.regValue .rdi := effect.writes.2.2.trans output
  have input : Bytes v.external (stackPtr s-112) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)) := by
    rw [memory]
    exact digits_bytes pre state
  obtain ⟨u,m,called,su,ip,bytes,ag⟩ := copy_call pre frame effect.rip source dest
    effect.writes.2.1 input
  refine ⟨u,n+m,run.trans called,su,ip,?_,bytes⟩
  exact ((effect.agrees.trans ag).read (n := 64) (r := 3)
    (by simp [copyArgumentsEffect,Effect.components,copyCallComponents])).trans output

end P256.Proofs.Projective.Multiply.Machine.Radix
