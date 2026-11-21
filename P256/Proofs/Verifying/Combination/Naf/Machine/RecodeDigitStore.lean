import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Memory
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitStore

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar P256.Proofs.Common.Instructions
open DigitMachine

theorem digit_store [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i w : Nat}
    (pre : Pre s boundary) (frame : FrameState s t) (rip : t.RIP = 0x10f495)
    (rsi : t.regValue .rsi = s.regValue .rdi) (r14 : t.regValue .r14 = BitVec.ofNat 64 i)
    (index : i<256) (rdx : (t.regValue .rdx).setWidth 8 = BitVec.ofInt 8 (digit w)) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u ∧ u.RIP = 0x10f499 ∧
      u.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
        some (UInt8.ofNat (BitVec.ofInt 8 (digit w)).toNat) ∧
      AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 i) 1,.rip] t u ∧
      MemoryWriteFrame t u #v[digitRegion s i 1] := by
  have len : 3 + (AddrMode.sib 6 (some 14) 0 .none).tail.length = 4 := rfl
  have address : storeAddrAt 0x10f495 (.sib 6 (some 14) 0 .none) 4 t =
      s.regValue .rdi+BitVec.ofNat 64 i := by
    change t.regValue .rsi+(t.regValue .r14 <<< 0)+0#64 = _
    rw [BitVec.shiftLeft_zero, BitVec.add_zero, rsi, r14]
  obtain ⟨u,run,ready,effect⟩ :=
    (mov_m8_r8_effect_step 0x10f495 0x42 (by simp [RexPrefix]) 2
      (.sib 6 (some 14) 0 .none) (by decide +kernel) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xf495 _ (by decide) (by decide +kernel))
      ⟨rip, by rw [len, address]; exact output_writable pre frame (by omega),
        by rw [len, address]; exact output_code pre (pc := 0xf495) (by omega) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf499 (by decide)))
  have agrees : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 i) 1,.rip] t u := by
    simpa only [storeEffect_components, len, address] using effect.agrees
  obtain ⟨frameU,memory⟩ := output_after pre frame (i := i) (len := 1) (by omega) ready agrees
    (by simp [Component.Covers]) (by simp)
  refine ⟨u,run,frameU,effect.rip,?_,agrees,memory⟩
  have value : memLoad u.external (s.regValue .rdi+BitVec.ofNat 64 i) 8 =
      BitVec.ofInt 8 (digit w) := by
    have h := effect.writes
    change memLoad u.external (storeAddrAt 0x10f495 (.sib 6 (some 14) 0 .none) 4 t) 8 =
      (t.regValue .rdx).setWidth 8 at h
    simpa only [address, rdx] using h
  have byte := Bytes.of_memLoad (n := 8)
    (output_readable pre frameU (i := i) (len := 1) (by omega)).mem 0 (by decide)
  rw [value] at byte
  simpa only [BitVec.add_zero, storedByte, Nat.mul_zero, Nat.shiftRight_zero] using byte

theorem inc_index [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i : Nat}
    (pre : Pre s boundary) (frame : FrameState s t) (rip : t.RIP = 0x10f3d0)
    (r14 : t.regValue .r14 = BitVec.ofNat 64 i) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u ∧ u.RIP = 0x10f3d3 ∧
      u.regValue .r14 = BitVec.ofNat 64 (i+1) ∧
      AgreesExcept [.reg 14,.flags,.rip] t u := by
  obtain ⟨u,run,ready,effect⟩ :=
    (inc_r64_effect_step 0x10f3d0 0x49 0xc6 (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xf3d0 _ (by decide) (by decide +kernel))
      rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf3d3 (by decide)))
  have agrees : AgreesExcept [.reg 14,.flags,.rip] t u := effect.agrees
  refine ⟨u,run,frame.after_registers ready agrees (by simp [Component.Covers]) (by simp),
    effect.rip,?_,agrees⟩
  have h : u.regValue .r14 = t.regValue .r14+1 := effect.writes
  rw [r14] at h
  change u.regValue .r14 = BitVec.ofNat 64 i+1#64 at h
  simpa only [BitVec.ofNat_add] using h

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitStore
