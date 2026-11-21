import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Split.Caller (Site)

def retained (s : Site) (k : Nat) : List (Nat × Nat) := match s with
  | .roundSecond | .mulSecond => [(616,Site.mulFirst.value k)]
  | .mulLambda | .addFirst => [(176,Site.addSecond.value k)]
  | _ => []

def results (s : Site) (k : Nat) := (destination s, s.value k) :: retained s k

def Stored (sp : BitVec 64) (m : Ram) (xs : List (Nat × Nat)) :=
  ∀ kv ∈ xs, WordsAt m (slot sp kv.1) 64 (scalarWords kv.2)

structure Operand (site : Site) (sp : BitVec 64) (n : Ram) (p : BitVec 64) (v : Nat) : Prop where
  words : WordsAt n p 64 (scalarWords v)
  read : Readable n p 32
  stack : p.toNat + 32 ≤ (frameSp sp-8).toNat - site.window ∨ (frameSp sp-8).toNat + 8 ≤ p.toNat
  dest : p.toNat + 32 ≤ (slot sp (destination site)).toNat ∨ (slot sp (destination site)).toNat+32 ≤ p.toNat

variable {a : Registers} {m n : Ram} {sp scalar : BitVec 64} {k : Nat}

private theorem fromSlot (e : RoutineEntry a m sp 0x558) (f : RamWriteFrame m n [scratch sp 0x558])
    (s : Site) {i v : Nat} (hi : i+32 ≤ 696) (sep : i+32 ≤ destination s ∨ destination s+32 ≤ i)
    (w : WordsAt n (slot sp i) 64 (scalarWords v)) : Operand s sp n (slot sp i) v := by
  obtain ⟨_,_,destHi,_⟩ := bounds s
  exact ⟨w,((e.stack.of_frame f).sub (by split_bounds e) (by split_bounds e)).readable,
    Or.inr (by split_bounds e),by split_bounds e⟩

private theorem fromParameter (e : RoutineEntry a m sp 0x558) (f : RamWriteFrame m n [scratch sp 0x558])
    (s : Site) {p : BitVec 64} {v : Nat} (h : (p,v) ∈ Generate.Generator.Multiply.Split.parameters) :
    Operand s sp n p v := by
  obtain ⟨_,hw,dh,_⟩ := bounds s
  have par := Generate.Generator.Multiply.Split.parameterAt (Recode.imageFromFrame e f) h
  have sep := par.apart (e.stack.of_frame f) (by decide)
  exact ⟨par.words,par.readable,by split_bounds e,by split_bounds e⟩

set_option maxHeartbeats 600000 in
theorem operands (site : Site) (later : site ≠ .roundFirst) (entry : RoutineEntry a m sp 0x558)
    (f : RamWriteFrame m n [scratch sp 0x558])
    (words : WordsAt m scalar 64 (scalarWords k)) (read : Readable m scalar 32)
    (apart : Outside [scratch sp 0x558] scalar 32) (old : Stored sp n (results site.prev k)) :
    Operand site sp n (left sp scalar site) (site.x k) ∧ Operand site sp n (right sp site) (site.y k) := by
  have external : Operand site sp n scalar k := by
    obtain ⟨_,hw,dh,_⟩ := bounds site
    have sep := apart.2 _ (.head _)
    exact ⟨words.of_frame f (by decide) apart,read.of_frame f,by split_bounds entry,by split_bounds entry⟩
  cases site with
  | roundFirst => contradiction
  | mulFirst =>
    exact ⟨fromSlot entry f .mulFirst (i := 56) (by decide) (by decide) (old (56,Site.roundFirst.value k) (.head _)),
      fromParameter entry f .mulFirst (p := 0x202220) (v := Generate.Curve.minusB1) (by decide +kernel)⟩
  | roundSecond => exact ⟨external,fromParameter entry f .roundSecond (p := 0x202240) (v := Generate.Curve.g2) (by decide +kernel)⟩
  | mulSecond =>
    exact ⟨fromSlot entry f .mulSecond (i := 56) (by decide) (by decide) (old (56,Site.roundSecond.value k) (.head _)),
      fromParameter entry f .mulSecond (p := 0x202260) (v := Generate.Curve.minusB2) (by decide +kernel)⟩
  | addSecond =>
    exact ⟨fromSlot entry f .addSecond (i := 616) (by decide) (by decide) (old (616,Site.mulFirst.value k) (.tail _ (.head _))),
      fromSlot entry f .addSecond (i := 224) (by decide) (by decide) (old (224,Site.mulSecond.value k) (.head _))⟩
  | mulLambda =>
    exact ⟨fromSlot entry f .mulLambda (i := 176) (by decide) (by decide) (old (176,Site.addSecond.value k) (.head _)),
      fromParameter entry f .mulLambda (p := 0x202280) (v := domain.n - Generate.Curve.eigenvalue) (by decide +kernel)⟩
  | addFirst => exact ⟨external,fromSlot entry f .addFirst (i := 256) (by decide) (by decide) (old (256,Site.mulLambda.value k) (.head _))⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
