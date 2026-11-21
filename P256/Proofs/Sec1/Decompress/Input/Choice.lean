import P256.Proofs.Sec1.Decompress.Input.Converted
import P256.Proofs.Sec1.Decompress.Select.Sign.Bit
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open P256.Proofs.Common.Instructions.MovzxByte

structure Chosen [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10fcfc
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  output : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi
  valid : t.regValue .rax = if x < P256.Spec.Operations.domain.p then 1 else 0
  r14 : t.regValue .r14 = 0xffffffff00000001
  r15 : t.regValue .r15 = stackPtr s - 408
  value : Field.MontgomeryAt t (stackPtr s - 408) (x % P256.Spec.Operations.domain.p)

theorem choice [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : Converted s u (Encoding.octetsToNat bytes) odd) :
    ∃ fuel t, Advances boundary fuel u t ∧ Chosen s t (Encoding.octetsToNat bytes) odd := by
  obtain ⟨v, runV, readyV, effectV⟩ :=
    (movzx_r32_r8_effect_step 0x10fcf4 0xfb rfl (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xfcf4
        [0x0f,0xb6,0xfb] (by decide) (by decide +kernel)) state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfcf7 (by decide)))
  change (movzxR32R8Effect 0x10fcf4 3 7 3 u).Holds u v at effectV
  have agreesV : AgreesExcept [.reg 7,.rip] u v := effectV.agrees
  have frameV := state.toFrameState.after_registers readyV agreesV
    (by simp [Component.Covers]) (by simp)
  have memoryV := agreesV.external (by simp [Component.Covers])
  obtain ⟨n, t, runT, frameT, rip, valid, agreesT⟩ := Select.Sign.choice_call pre.toCalleePre frameV
    0xfcf7 0x9374 (by decide) (by decide +kernel) (by decide) effectV.rip
  refine ⟨1+n, t, runV.trans runT, ⟨frameT, rip, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := Select.Sign.read_preserved agreesT (offset := 332) (n := 32)
      (by decide) (by decide)
    change memLoad t.external (stackPtr s-332) 32 = memLoad v.external (stackPtr s-332) 32 at h
    rw [memoryV] at h
    exact h.trans state.parity
  · have h := Select.Sign.read_preserved agreesT (offset := 224) (n := 64)
      (by decide) (by decide)
    change memLoad t.external (stackPtr s-224) 64 = memLoad v.external (stackPtr s-224) 64 at h
    rw [memoryV] at h
    exact h.trans state.output
  · have hx := effectV.writes
    change v.regValue .rdi = ((u.regValue .rbx).setWidth 8).setWidth 64 at hx
    change t.regValue .rax = ((v.regValue .rdi).setWidth 8).setWidth 64 at valid
    rw [hx, state.valid] at valid
    by_cases hx : Encoding.octetsToNat bytes < P256.Spec.Operations.domain.p
    · simpa [hx] using valid
    · simpa [hx] using valid
  · exact ((agreesT.read (n := 64) (r := 14) (by simp [Select.Sign.components])).trans
      (agreesV.read (n := 64) (r := 14) (by simp))).trans state.r14
  · exact ((agreesT.read (n := 64) (r := 15) (by simp [Select.Sign.components])).trans
      (agreesV.read (n := 64) (r := 15) (by simp))).trans state.r15
  · apply state.value.of_bytes_eq
    intro i hi
    have h := Select.Sign.byte_preserved agreesT (offset := 408) (len := 32)
      (by decide) (by decide) hi
    rw [memoryV] at h
    exact h

end P256.Proofs.Sec1.Decompress.Input
