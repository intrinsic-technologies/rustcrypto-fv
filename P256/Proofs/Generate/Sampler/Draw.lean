import P256.Proofs.Generate.Sampler.Read
import P256.Proofs.Generate.Sampler.Copy
import P256.Proofs.Generate.Sampler.Decode
import P256.Proofs.Generate.Sampler.Tag
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem draw [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : Nat} (pre : Pre s boundary input)
    (state : ReadReady s t input offset) (available : offset+32 ≤ input.size) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      LoopReady s u input offset
        (if Arith.uint (input.extract offset (offset+32)) < Operations.domain.n
          then 0x100c00 else 0x100ce5) 32 ∧
      u.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)) ∧
      Nat256At u (stackPtr s-184#64) (Arith.uint (input.extract offset (offset+32))) := by
  obtain ⟨a,⟨na,ha⟩,sa,remainingA⟩ := read_setup_correct pre state available
  obtain ⟨b,⟨nb,hb⟩,sb,remainingB,bytes⟩ := copy_correct pre sa available remainingA
  obtain ⟨c,⟨nc,hc⟩,sc,remainingC,value,tag⟩ := decode_call pre sb remainingB bytes
  have load : memLoad c.external (stackPtr c+112#64) 8 =
      (if Arith.uint (input.extract offset (offset+32)) < Operations.domain.n then 1 else 0) := by
    have addr : stackPtr c+112#64 = stackPtr s-152#64 :=
      scalar_stack_address (frameOffset := 264) sc.rsp (by decide) (by decide)
    have window : Bytes c.external (stackPtr s-152#64) 1
        (fun _ => if Arith.uint (input.extract offset (offset+32)) < Operations.domain.n then 1 else 0) := by
      intro i hi
      have iz : i=0 := by omega
      subst i
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using tag
    have h := window.loadByte 0 (by decide)
    rw [addr]
    simp only [BitVec.add_zero] at h
    split <;> rename_i test
    · rw [ite_eq_left test] at h
      exact h
    · rw [ite_eq_right test] at h
      exact h
  obtain ⟨u,⟨nd,hd⟩,su,rip,agrees⟩ := tag_branch pre sc.toState sc.rip
  rw [load] at rip
  have out : u.RIP = if Arith.uint (input.extract offset (offset+32)) < Operations.domain.n
      then 0x100c00 else 0x100ce5 := by
    by_cases valid : Arith.uint (input.extract offset (offset+32)) < Operations.domain.n
    · simpa only [ite_eq_left valid,ite_eq_left (show (1:BitVec 8)=1 from rfl),ite_true] using rip
    · simpa only [ite_eq_right valid,ite_eq_right (by decide : ¬(0:BitVec 8)=1)] using rip
  have ext := agrees.external (by simp [Component.Covers])
  refine ⟨u,⟨na+nb+nc+nd,((ha.trans hb).trans hc).trans hd⟩,
    {toState := su,rip := out,descriptor := ?_,source := ?_,remaining := ?_,
      decoded := ?_,buffer := ?_,output := ?_},?_,?_⟩
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans sc.descriptor
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans sc.source
  · exact (agrees.read (n := 64) (r := 13) (by simp)).trans sc.remaining
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans sc.decoded
  · exact (agrees.read (n := 64) (r := 12) (by simp)).trans sc.buffer
  · rw [ext]
    exact sc.output
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans remainingC
  · simpa only [Nat256At,ext] using value

end P256.Proofs.Generate.Sampler
