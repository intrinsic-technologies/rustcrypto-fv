import K256.Proofs.Generate.Generator.Multiply.Radix.Extract
import K256.Proofs.Generate.Generator.Multiply.Radix.Pair
import K256.Proofs.Generate.Generator.Multiply.Radix.Return

namespace K256.Proofs.Generate.Generator.Multiply.Radix

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

theorem execute {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (x : Nat)
    (bound : x < 2^128)
    (atoms : Atom.All code args mem (Fn11aa40.frameAt .l11aa40 fr))
    (src : Readable mem fr.rsi 16)
    (lo : memLoad mem fr.rsi 64 = BitVec.ofNat 64 x)
    (hi : memLoad mem (fr.rsi + 8) 64 = BitVec.ofNat 64 (x / 2^64))
    (dst : Writable code mem fr.rdi 33)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l11aa40, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn11aa40.doneAt fr) ∧
      out.values[0] = ⟨64, fr.rdi⟩ ∧ ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 8 (Vector.ofFn fun i : Fin 33 => byte x i.val) ∧
      RamWriteFrame mem out.store [⟨(fr.rsp - 33).toNat, 33⟩, ⟨fr.rdi.toNat, 33⟩] := by
  obtain ⟨b, n, start, init⟩ := extractNibbles included fr args mem x bound atoms src lo hi srcAbove
  have reach (k : Nat) (hk : k ≤ 16) :
      ∃ a m, Path code .l11ac00 b n (loopLabel (2*k)) a m ∧ LoopState code fr mem m a x (2*k) := by
    induction k with
    | zero => exact ⟨b, n, .refl _, init⟩
    | succ k ih =>
      obtain ⟨c, p, prev, inv⟩ := ih (by omega)
      have here : loopLabel (2*k) = .l11ac00 := ite_eq_right (by omega)
      rw [here] at prev
      obtain ⟨t, u, step, next⟩ := carryPair included bound (by omega) inv
      exact ⟨t, u, prev.trans step, next⟩
  obtain ⟨c, p, last, inv⟩ := reach 16 (by decide)
  obtain ⟨o, ret, rest⟩ := copyDigits included bound inv dst dstAbove
  exact ⟨o, Program.Exec.of_sem ((start.trans last).exec ret.sem), rest⟩

end K256.Proofs.Generate.Generator.Multiply.Radix
