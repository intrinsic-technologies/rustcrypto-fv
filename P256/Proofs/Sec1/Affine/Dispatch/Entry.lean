import P256.Proofs.Sec1.Affine.Prefix
import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Tagged [Bindings] (s t : RamState) (tag : UInt8) : Prop extends Frame s t where
  output : t.regValue .rbx = s.regValue .rdi
  input : t.regValue .rsi = s.regValue .rsi
  tagRegister : t.regValue .rax = tag.toBitVec.setWidth 64
  tagCopy : t.regValue .rcx = tag.toBitVec.setWidth 64
  carry : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
    (cmpSpec (tag.toBitVec.setWidth 32 - 2) 4).CF

theorem tag_entry [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) :
    ∃ fuel t, Advances boundary fuel s t ∧ Tagged s t (bytes.data[0]?.getD 0) ∧
      t.RIP = 0x1100f0 := by
  obtain ⟨u, entry⟩ := prologue pre
  have frame := entry.frame pre
  have input : u.regValue .rsi = s.regValue .rsi :=
    entry.agrees.read (n := 64) (r := 6) (by simp [saveComponents, saveFrame])
  have output : u.regValue .rdi = s.regValue .rdi :=
    entry.agrees.read (n := 64) (r := 7) (by simp [saveComponents, saveFrame])
  have load : memLoad u.external (u.regValue .rsi) 8 = (bytes.data[0]?.getD 0).toBitVec := by
    rw [input]
    apply P256.Proofs.Common.Memory.memLoad8_of_byte
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (input_of_frame pre frame.frame).2 0 (by decide)
  have preU : PrefixPre u := by
    refine ⟨entry.rip, ?_⟩
    rw [input]
    have readable := input_readable pre frame
    exact ⟨by have := readable.low; omega, fun i hi => readable.mem i (by omega)⟩
  obtain ⟨fuel, t, run, ready, _, effect⟩ := prefix_correct boundary pre.outerBoundary u
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x100e1 prefixBytes
      (by decide) (by decide +kernel)) preU
  have agrees : AgreesExcept [.reg 3, .reg 0, .reg 1, .reg 2, .flags, .rip] u t :=
    effect.agrees
  have state := frame.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  change t.regValue .rbx = u.regValue .rdi ∧
    t.regValue .rax = (memLoad u.external (u.regValue .rsi) 8).setWidth 64 ∧
    t.regValue .rcx = (memLoad u.external (u.regValue .rsi) 8).setWidth 64 ∧
    t.regValue .rdx = ((memLoad u.external (u.regValue .rsi) 8).setWidth 32 - 2).setWidth 64 at writes
  rw [load] at writes
  refine ⟨7 + fuel, t, entry.execution.trans run, ⟨state, writes.1.trans output,
    (agrees.read (n := 64) (r := 6) (by simp)).trans input, writes.2.1, writes.2.2.1, ?_⟩,
    effect.rip⟩
  have flags := effect.flags.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).CF =
    (cmpSpec ((memLoad u.external (u.regValue .rsi) 8).setWidth 32 - 2) 4).CF at flags
  rwa [load] at flags

end P256.Proofs.Sec1.Affine
