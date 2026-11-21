import P256.Proofs.Signing.Core.Iteration.Components.PrefixRun
import P256.Proofs.Signing.Core.Iteration.Components.Read
import P256.Proofs.Signing.Core.Iteration.Components.ReduceSetupRun
import P256.Proofs.Signing.Core.Iteration.Components.ReduceCall
import P256.Proofs.Signing.Core.Iteration.Components.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

structure Reduced [Bindings] (s t : RamState) (state : Nonce.State) (nonce x y : Nat)
    (digest : ByteArray) : Prop where
  frame : Frame s t
  values : Values s t state nonce x y digest
  registers : Registers s t
  value : Nat256At t (frameBase s+176) (x % Operations.domain.n)

theorem reduce_x [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {nonce x y : Nat} {digest : ByteArray} (hp : SignPre s boundary)
    (input : ComponentsInput s t state nonce x y digest) (rip : t.RIP = 0x10d19f) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d272 ∧
      Reduced s u state nonce x y digest := by
  let initial : Values s t state nonce x y digest :=
    ⟨input.arguments,input.generator,input.encoded.point,input.inverse,input.digest⟩
  obtain ⟨na,a,runA,frameA,ea⟩ := Prefix.run hp input.encoded.frame rip
  rcases ea.writes with ⟨_,_,_,_,_,_,count,limbs,source,destination,bits⟩
  have valuesA := initial.copy (fun off live => Prefix.byte input.encoded.frame ea
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have bytesA : (MemoryRegion.mk (frameBase s+432).toNat 32).HasBytes a.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x) := by
    apply hasBytes_copy input.encoded.encoded
    intro i hi
    have h := Prefix.byte input.encoded.frame ea (offset := 432+i)
      (by omega) (by omega) (.inl (by omega)) (.inl (by omega))
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using h
  have rbpA : a.regValue .rbp = frameBase s+528 :=
    (ea.agrees.read (n := 64) (r := 5) (by simp [Prefix.effect,Effect.components])).trans input.encoded.rbp
  have r13A : a.regValue .r13 = frameBase s+432 :=
    (ea.agrees.read (n := 64) (r := 13) (by simp [Prefix.effect,Effect.components])).trans input.encoded.r13
  have r15A : a.regValue .r15 = frameBase s+1328 :=
    (ea.agrees.read (n := 64) (r := 15) (by simp [Prefix.effect,Effect.components])).trans input.encoded.r15
  have bound : x < 2^256 := Nat.lt_trans input.encoded.point.1.1 (by decide +kernel)
  obtain ⟨nb,b,runB,frameB,ripB,valueB,memB,regsB⟩ := read hp frameA ea.rip
    (source.trans input.encoded.r13) (destination.trans input.encoded.r15)
    count limbs bits bound bytesA
  have valuesB := valuesA.copy (fun off live => memB off
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have rbpB := (regsB .rbp (by simp)).trans rbpA
  have r13B := (regsB .r13 (by simp)).trans r13A
  have r15B := (regsB .r15 (by simp)).trans r15A
  obtain ⟨nc,c,runC,frameC,ec⟩ := ReduceSetup.run hp frameB ripB
  have valuesC := valuesB.copy (fun off live => ReduceSetup.byte frameB ec
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  have valueC := ReduceSetup.copied hp frameB frameC ec valueB
  have rbpC : c.regValue .rbp = frameBase s+528 :=
    (ec.agrees.read (n := 64) (r := 5) (by simp [ReduceSetup.effect,Effect.components])).trans rbpB
  have r13C : c.regValue .r13 = frameBase s+432 :=
    (ec.agrees.read (n := 64) (r := 13) (by simp [ReduceSetup.effect,Effect.components])).trans r13B
  have r15C : c.regValue .r15 = frameBase s+1328 :=
    (ec.agrees.read (n := 64) (r := 15) (by simp [ReduceSetup.effect,Effect.components])).trans r15B
  have regsC : Registers s c :=
    ⟨rbpC,r13C,ec.writes.1.trans (congrArg (·+2160) frameB.rsp),r15C⟩
  obtain ⟨nd,d,runD,frameD,ripD,valueD,memD,regsD⟩ := reduce hp frameC ec.rip
    (ec.writes.2.2.2.2.1.trans rbpB)
    (ec.writes.2.2.2.1.trans (congrArg (·+176) frameB.rsp)) valueC
  have valuesD := valuesC.copy (fun off live => memD off
    (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega))
  exact ⟨na+nb+nc+nd,d,((runA.trans runB).trans runC).trans runD,ripD,
    ⟨frameD,valuesD,regsC.copy regsD,valueD⟩⟩

end P256.Proofs.Signing.Core.Iteration.Components
