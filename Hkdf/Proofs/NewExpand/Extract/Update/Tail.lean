import Hkdf.Proofs.NewExpand.Extract.Update.TailLength
import Hkdf.Proofs.NewExpand.Extract.Update.Message
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem afterCopy {initial s t : RamState} {count : Nat} (stack : Stack.Valid initial 2264)
    (frame : MemoryWriteFrame s t #v[⟨(base initial + 120).toNat, count⟩,
      ⟨(stackPtr initial - 464).toNat, 8⟩])
    (i : Nat) (lo : count ≤ i) (hi : i < 144) :
    t.external[base initial + 120 + BitVec.ofNat 64 i]? =
      s.external[base initial + 120 + BitVec.ofNat 64 i]? := by
  have bounds := CallFrame.stack_bounds stack
  have addr : base initial + 120 = stackPtr initial - 336 := by unfold base; bv_omega
  have buffer := CallFrame.stack_sub_toNat stack (offset := 336) (by decide)
  have push := CallFrame.stack_sub_toNat stack (offset := 464) (by decide)
  change (stackPtr initial - 336).toNat = _ at buffer
  change (stackPtr initial - 464).toNat = _ at push
  have pos : (base initial + 120 + BitVec.ofNat 64 i).toNat = (base initial + 120).toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (by rw [addr, buffer]; omega)]
  apply frame
  intro region member inside
  rcases (show region = ⟨(base initial + 120).toNat, count⟩ ∨
      region = ⟨(stackPtr initial - 464).toNat, 8⟩ by simpa using member) with rfl | rfl
  · have right := inside.2
    change (base initial + 120 + BitVec.ofNat 64 i).toNat < (base initial + 120).toNat + count at right
    omega
  · have right := inside.2
    change (base initial + 120 + BitVec.ofNat 64 i).toNat < (stackPtr initial - 464).toNat + 8 at right
    rw [pos, addr, buffer, push] at right
    omega

theorem afterStore {initial s t : RamState}
    (frame : AgreesExcept [.mem (base initial + 183) 1,.rip] s t)
    (i : Nat) (apart : i ≠ 63) (hi : i < 144) :
    t.external[base initial + 120 + BitVec.ofNat 64 i]? =
      s.external[base initial + 120 + BitVec.ofNat 64 i]? := by
  apply outsideByteStore frame
  intro eq
  have b : BitVec.ofNat 64 i = 63 := by bv_omega
  have n := congrArg BitVec.toNat b
  simp only [BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.mod_eq_of_lt (show i < 2^64 by omega)] at n
  exact apart n

theorem tailAfterStore {initial s t : RamState} {ikm : ByteArray}
    (frame : AgreesExcept [.mem (base initial + 183) 1,.rip] s t)
    (tail : (⟨(base initial + 120).toNat, ikm.size % 64⟩ : MemoryRegion).HasBytes
      s.external (SHA256.remainderBytes ikm)) :
    (⟨(base initial + 120).toNat, ikm.size % 64⟩ : MemoryRegion).HasBytes
      t.external (SHA256.remainderBytes ikm) := by
  refine ⟨tail.1, fun i => ?_⟩
  have hi := i.isLt
  have size : (SHA256.remainderBytes ikm).size = ikm.size % 64 := tail.1
  have same := afterStore frame i.val (by omega) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    same.trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using tail.2 i)

theorem shortJump [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (frame : Frame initial s boundary)
    (rip : s.RIP = 0x10fc82) (hmac : HmacAt s (base initial + 120)
      (salt.getD (RFC5869.defaultSalt .sha256)) ikm) :
    ∃ t, Updated initial t boundary salt ikm := by
  have instr := jmp_rel8_effect_step 0x10fc82 0x47 (by decide)
  obtain ⟨t, run, ready, effect⟩ := instr.advances (supportedMachine_readyToStep frame.machine)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xfc82 [0xeb,0x47] (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xfccb (by decide)))
  have agrees : AgreesExcept [.rip] s t := effect.agrees
  have ext := agrees.external (by simp [Component.Covers])
  exact ⟨t, registerFrame pre frame run ready agrees (by simp [Component.Covers])
    (by decide) (by decide) (by decide) (by decide), effect.rip,
    hmac.of_copy (fun i _ => by rw [ext])⟩

end Hkdf.Proofs.NewExpand.Extract.Update
