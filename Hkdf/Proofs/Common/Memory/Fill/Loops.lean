import Hkdf.Proofs.Common.Memory.Fill.Memory
import Hkdf.Proofs.Common.Memory.Fill.Stos

set_option autoImplicit false

open Hkdf.Proofs.Program

open Hkdf.Proofs.Common.Machine (CalleePre)

namespace Hkdf.Proofs.Common.Memory.Fill

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem FillState.repStosb [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve count more : Nat} {p : BitVec 64}
    (hp : CalleePre s boundary 0x10dd10 0 n reserve)
    (h : FillState s t count) (hcount : count + more ≤ n)
    (hrip : t.RIP = p) (hc : rcx.read t = BitVec.ofNat 64 more)
    (hz : t.regValue .rax = 0)
    (hcode : CodeIn (codeRange p [0xf3, 0xaa]) t)
    (hprog : ∀ i < 2, InProgram (p + BitVec.ofNat 64 i))
    (hend : p + 2 ≠ boundary.rip) :
    ∃ u, Advances boundary (max more 1) t u ∧ FillState s u (count+more) ∧
      u.RIP = p + 2#64 ∧ rcx.read u = 0 ∧
      AgreesExcept [.reg 1, .reg 7, .mem (t.regValue .rdi) more, .rip] t u := by
  have hd := h.destinationReadable hp hcount
  have hstart : p ≠ boundary.rip := by
    intro he
    apply hp.outerBoundary
    have hi := hprog 0 (by decide)
    simpa only [BitVec.add_zero, he] using hi
  have hal : (Operand.reg 0 : Operand 8).read t = 0 := by
    change (t.regValue .rax).setWidth 8 = 0
    rw [hz]
    rfl
  obtain ⟨u, ha, hr, hi, hdi, hcx, hfill, he⟩ := Stos.rep_stosb_zero_fill hp.stride boundary p t more
    h.ready hcode hrip hc (h.agrees.directionFlagClear (by simp [fillComponents, registerComponents]) hp.directionFlag).df hal
    hd.low hd.mem (fun hpos => h.destinationTables hp hcount hpos)
    (h.destinationCodeApart (bytes := [0xf3, 0xaa]) hp hcount hprog) hstart hend
  refine ⟨u, ha, h.append ?_ hr hdi hfill he, hi, hcx, he⟩
  have hn : (s.regValue .rdi).toNat + n < 2^32 := hp.outputBounded
  omega

theorem FillState.repStosq [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve count words : Nat} {p : BitVec 64}
    (hp : CalleePre s boundary 0x10dd10 0 n reserve)
    (h : FillState s t count) (hcount : count + 8*words ≤ n)
    (hrip : t.RIP = p) (hc : rcx.read t = BitVec.ofNat 64 words)
    (hz : t.regValue .rax = 0)
    (halign : 0 < words → (t.regValue .rdi).toNat % 8 = 0)
    (hcode : CodeIn (codeRange p [0xf3, 0x48, 0xab]) t)
    (hprog : ∀ i < 3, InProgram (p + BitVec.ofNat 64 i))
    (hend : p + 3 ≠ boundary.rip) :
    ∃ u, Advances boundary (max words 1) t u ∧ FillState s u (count+8*words) ∧
      u.RIP = p + 3#64 ∧ rcx.read u = 0 ∧
      AgreesExcept [.reg 1, .reg 7, .mem (t.regValue .rdi) (8*words), .rip] t u := by
  have hd := h.destinationReadable hp hcount
  have hstart : p ≠ boundary.rip := by
    intro he
    apply hp.outerBoundary
    have hi := hprog 0 (by decide)
    simpa only [BitVec.add_zero, he] using hi
  obtain ⟨u, ha, hr, hi, hdi, hcx, hfill, he⟩ := Stos.rep_stosq_zero_fill hp.stride boundary p t words
    h.ready hcode hrip hc (h.agrees.directionFlagClear (by simp [fillComponents, registerComponents]) hp.directionFlag).df hz
    hd.low hd.mem (fun hpos => h.destinationTables hp hcount (by omega))
    (h.destinationCodeApart (bytes := [0xf3, 0x48, 0xab]) hp hcount hprog) halign hstart hend
  refine ⟨u, ha, h.append ?_ hr hdi hfill he, hi, hcx, he⟩
  have hn : (s.regValue .rdi).toNat + n < 2^32 := hp.outputBounded
  omega

end Hkdf.Proofs.Common.Memory.Fill
