import P256.Proofs.Sec1.Decompress.Input.Parity
import P256.Proofs.Sec1.Decompress.Input.Load
import P256.Proofs.Program.ScalarFrame.Input

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

structure Decoded [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10fc30
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  output : t.regValue .rdi = s.regValue .rdi
  high : t.regValue .rax = BitVec.ofNat 64 (x / 2^192)
  third : t.regValue .rcx = BitVec.ofNat 64 (x / 2^128)
  second : t.regValue .r8 = BitVec.ofNat 64 (x / 2^64)
  low : t.regValue .rdx = BitVec.ofNat 64 x

theorem decode [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd) :
    ∃ fuel t, Advances boundary fuel s t ∧ Decoded s t (Encoding.octetsToNat bytes) odd := by
  obtain ⟨u, ru, su, pu, gu⟩ := prologue pre
  obtain ⟨v, rv, sv, pv, parity, gv⟩ := store_parity pre su pu
  have source : v.regValue .rsi = s.regValue .rsi :=
    (gu.trans gv).read (n := 64) (r := 6) (by simp [saveFrame])
  have output : v.regValue .rdi = s.regValue .rdi :=
    (gu.trans gv).read (n := 64) (r := 7) (by simp [saveFrame])
  have input : (registerRegion v .rsi 32).HasBytes v.external bytes := by
    simpa only [registerRegion, source] using sv.input_bytes pre.toCalleePre pre.input
  have hp : InputLoadPre v := by
    refine ⟨pv, ?_⟩
    intro i hi
    change MemReadable v (v.regValue .rsi + i) 8
    rw [source]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      have bound : (s.regValue .rsi).toNat + 32 < 2^32 := pre.inputBounded
      exact readable_of_grow
        (memoryRegion_memReadable pre.inputBounded pre.inputAllocated
          (by simp [registerRegion] <;> omega)
          (by simp [registerRegion] <;> omega)) sv.allocated
  obtain ⟨n, t, run, ready, _, rip, high, third, second, low, agrees⟩ :=
    input_load_nat pre.outerBoundary (readyToStep sv.machine sv.bindingsSupported)
      sv.loaded hp input
  have st := sv.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨7+1+n, t, (ru.trans rv).trans run,
    ⟨st, rip, ?_, (agrees.read (n := 64) (r := 7) (by simp)).trans output,
      high, third, second, low⟩⟩
  rw [memory, parity]
  have rd : u.regValue .rdx = s.regValue .rdx :=
    gu.read (n := 64) (r := 2) (by simp [saveFrame])
  rw [rd, pre.parity]
  exact BitVec.setWidth_ofNat_of_le (by decide) _

end P256.Proofs.Sec1.Decompress.Input
