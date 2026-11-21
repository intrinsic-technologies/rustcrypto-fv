import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Program.Copy.Prologue
import P256.Proofs.Program.Copy.Body
import P256.Proofs.Program.Copy.Loops
import P256.Proofs.Program.Copy.Return

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)
open P256.Proofs.Program.Copy (CopyState copyComponents destinationLow finish middle registerComponents tailCount)

namespace P256.Proofs.Program

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memcpy_inProgram (offset : Nat) (h : offset < 47) :
    InProgram ((0x11c930 : BitVec 64) + BitVec.ofNat 64 offset) := by
  have hi := inProgram_of_textOffset (0x1c930+offset) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hi
  exact hi

theorem memcpy_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {n stackReserve : Nat} (hp : CalleePre s boundary 0x11c930 n n stackReserve)
    (hrdx : s.regValue .rdx = BitVec.ofNat 64 n) (hn : n < 2^32) :
    ∃ final, CalleeResult s final boundary n stackReserve ∧
      (∀ i < n, final.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
        s.external[s.regValue .rsi + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (copyComponents s n ++ [.reg 4, .rip]) s final := by
  let head := min n ((8 - (s.regValue .rdi).toNat % 8) % 8)
  have hhead : head ≤ n := Nat.min_le_left _ _
  have hhead8 : head < 8 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.mod_lt _ (by decide))
  obtain ⟨s1, a1, hr1, hc1, hi1, h81, hx1, he1⟩ := memcpy_prologue
    (readyToStep hp.machine hp.bindingsSupported) (programLoaded_codeIn hp.loaded)
    hp.outerBoundary hp.rip hrdx (by omega)
  have h1 : CopyState s s1 0 := (CopyState.start (readyToStep hp.machine hp.bindingsSupported)).registers
    hr1 (he1.mono (by simp [registerComponents]))
  have code1 := programText_slice hc1 0x1c947 [0xf3,0xa4] (by decide) (by decide +kernel)
  obtain ⟨s2, a2, h2, hi2, _, he2⟩ := h1.repMovsb hp (more := head) (by omega) hi1 hx1 code1
    (by intro i hi; have ht := memcpy_inProgram (23+i) (by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht; exact ht)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c949 (by decide)))
  have h2' : CopyState s s2 head := by simpa only [Nat.zero_add] using h2
  have dx2 : s2.regValue .rdx = BitVec.ofNat 64 n :=
    (he2.read (n := 64) (r := 2) (by simp)).trans
      ((he1.read (n := 64) (r := 2) (by decide)).trans hrdx)
  have r82 : s2.regValue .r8 = BitVec.ofNat 64 head :=
    (he2.read (n := 64) (r := 8) (by simp)).trans h81
  obtain ⟨s3, a3, h3, hi3, dx3, cx3⟩ := middle hp h2' hhead (by omega) hi2 dx2 r82
  have hbulk : head + 8*((n-head)/8) ≤ n := by omega
  have align3 : 0 < (n-head)/8 → (s3.regValue .rdi).toNat % 8 = 0 := by
    intro hpos
    have hd := destinationLow hp
    rw [h3.rdi, toNat_add_ofNat _ _ (by omega)]
    have halign : head = (8 - (s.regValue .rdi).toNat % 8) % 8 := by
      dsimp only [head] at *
      omega
    rw [halign]
    omega
  have code3 := programText_slice (programLoaded_codeIn (h3.loaded hp hhead))
    0x1c953 [0xf3,0x48,0xa5] (by decide) (by decide +kernel)
  obtain ⟨s4, a4, h4, hi4, _, he4⟩ := h3.repMovsq hp hbulk hi3 cx3 align3 code3
    (by intro i hi; have ht := memcpy_inProgram (35+i) (by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht; exact ht)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c956 (by decide)))
  have dx4 : s4.regValue .rdx = BitVec.ofNat 64 (n-head) :=
    (he4.read (n := 64) (r := 2) (by simp)).trans dx3
  obtain ⟨s5, a5, h5, hi5, cx5⟩ := tailCount hp h4 hbulk (by omega) hi4 dx4
  have htotal : head + 8*((n-head)/8) + (n-head)%8 = n := by omega
  have code5 := programText_slice (programLoaded_codeIn (h5.loaded hp hbulk))
    0x1c95c [0xf3,0xa4] (by decide) (by decide +kernel)
  obtain ⟨s6, a6, h6, hi6, _, _⟩ := h5.repMovsb hp (by omega) hi5 cx5 code5
    (by intro i hi; have ht := memcpy_inProgram (44+i) (by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht; exact ht)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c95e (by decide)))
  rw [htotal] at h6
  exact finish hp h6 hi6 (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6)))))

end P256.Proofs.Program
