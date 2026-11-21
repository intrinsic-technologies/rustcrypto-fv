import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Entry
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Interface
import P256.Proofs.Field.Schoolbook.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program
open P256.Proofs.Common.Field.SquareRoot.Multiply
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def wordsOfNat (x : Nat) : Vector (BitVec 64) 4 :=
  Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (x / 2^(64*i.val))

theorem wordsOfNat_value {x : Nat} (hx : x < 2^256) : wordsValue (wordsOfNat x) = x := by
  have h := P256.Proofs.Field.Schoolbook.packFour_limbsOfNat hx
  simp only [wordsValue, wordsOfNat, Vector.getElem_ofFn, BitVec.toNat_ofNat,
    limbsToNat]
  dsimp [P256.Proofs.Field.Schoolbook.packFour, P256.Proofs.Field.Schoolbook.limbsOfNat,
    P256.Proofs.Field.Montgomery.wordBase] at h ⊢
  omega

theorem modulus_words : wordsOfNat P256.Spec.Operations.domain.p =
    #v[0xffffffffffffffff#64, 0xffffffff#64, 0#64, 0xffffffff00000001#64] := by
  decide +kernel

theorem nat256_words {s : RamState} {addr : BitVec 64} {x : Nat}
    (h : Nat256At s addr x) (i : Fin 4) :
    (Operand.mem (addr+BitVec.ofNat 64 (8*i.val)) : Operand 64).read s = (wordsOfNat x)[i] := by
  change memLoad s.external (addr+BitVec.ofNat 64 (8*i.val)) 64 = (wordsOfNat x)[i.val]
  simpa only [wordsOfNat, Vector.getElem_ofFn] using
    Nat256At.memLoad_limb h i.val i.isLt

theorem prologue_inputs [Bindings] {s t : RamState} {entry : BitVec 64}
    {boundary : ReturnBoundary} {a b : Nat}
    (pre : MontgomeryPre s boundary entry)
    (ag : AgreesExcept (prologueComponents s) s t)
    (ha : Nat256At s (s.regValue .rsi) a) (hb : Nat256At s (s.regValue .rdx) b)
    (hp : Nat256At s (s.regValue .rcx) P256.Spec.Operations.domain.p)
    (hi : s.regValue .r8 = 1#64) : FirstRowInput t (wordsOfNat a) (wordsOfNat b) := by
  have fr := prologue_frame ag
  have hrsi : t.regValue .rsi = s.regValue .rsi :=
    ag.read (r := 6) (n := 64) (by simp [prologueComponents])
  have hrdx : t.regValue .rdx = s.regValue .rdx :=
    ag.read (r := 2) (n := 64) (by simp [prologueComponents])
  have hrcx : t.regValue .rcx = s.regValue .rcx :=
    ag.read (r := 1) (n := 64) (by simp [prologueComponents])
  have ha' : Nat256At t (s.regValue .rsi) a := by
    refine ⟨ha.1, ?_⟩
    intro i h
    rw [input_bytes pre.toBinaryFieldPre fr h]
    exact ha.2 i h
  have hb' : Nat256At t (s.regValue .rdx) b := by
    refine ⟨hb.1, ?_⟩
    intro i h
    rw [right_bytes pre.toBinaryFieldPre fr h]
    exact hb.2 i h
  have hp' : Nat256At t (s.regValue .rcx) P256.Spec.Operations.domain.p := by
    refine ⟨hp.1, ?_⟩
    intro i h
    rw [modulus_bytes pre fr h]
    exact hp.2 i h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hrsi]
    exact nat256_words ha' i
  · intro i
    rw [hrdx]
    exact nat256_words hb' i
  · intro i
    rw [hrcx, ← modulus_words]
    exact nat256_words hp' i
  · exact (ag.read (r := 8) (n := 64) (by simp [prologueComponents])).trans hi

end P256.Proofs.Sec1.SquareRoot.Montgomery
