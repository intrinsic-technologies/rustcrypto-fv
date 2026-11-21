import ChaCha20Poly1305.Proofs.Decrypt.DetachBase
import ChaCha20Poly1305.Proofs.Decrypt.ShortCore
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Functions

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Detached

@[refine_layout] def trimABI (_ : Lifted.Label) (fr : Activation) := Short.leafFrame fr ++ [.gpr 7 fr.rdi,.gpr 6 fr.rsi]

@[refine_layout] def trimCore (n : BitVec 64) : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => .l102020
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms _ _ fr _ := [.writable fr.rdi 24,.mem (fr.rdi+16) 64 n,.fact (fr.rsi.toNat≤n.toNat),
    .fact (fr.rdi.toNat+24≤0x102020 ∨ 0x10202b≤fr.rdi.toNat),
    .fact (fr.rdi.toNat+24≤fr.rsp.toNat ∨ fr.rsp.toNat+8≤fr.rdi.toNat)]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done _ fr _ := [.mem (fr.rdi+16) 64 fr.rsi]
  footprint _ fr := [⟨(fr.rdi+16).toNat,8⟩]

@[refine_layout] def trimFn (n : BitVec 64) := leafSpec () trimABI (trimCore n) () ()

set_option maxHeartbeats 600000
set_option maxRecDepth 7000
set_option pp.maxSteps 150

theorem trimBlocks (n : BitVec 64) : ∀ l, (Layout.withFrame trimABI abiOut (trimCore n)).BlockSimulation fnCode l := by
  intro l; cases l
  x86_refine [Copy.program,cmpSpec_CF,cmpSpec_ZF]
  all_goals first | assumption | (exfalso; bv_omega)

theorem trimCorrect (n : BitVec 64) : (trimFn n).Correct :=
  provedCallee () trimABI (trimCore n) () rfl () rfl (fun _ => rfl) (trimBlocks n) (.done rfl)

@[refine_layout] def emptyCore : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => .l102dc0
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms _ _ fr _ := [.fact (fr.rdx=0)]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done _ fr _ := [.gpr 0 fr.rdi]
  footprint _ _ := []

private theorem headZero (a : BitVec 64) : (if 0<a.toNat then (0:BitVec 64) else a)=0 := by
  split <;> bv_omega

private theorem noCopy (m : Ram) (d s : BitVec 64) : memCopy m d s 0=m := rfl

theorem emptyBlocks : ∀ l, (Layout.withFrame Fn102dc0.active abiOut emptyCore).BlockSimulation fnCode l := by
  intro l; cases l
  x86_refine [Copy.program,cmpSpec_CF,decide_eq_true_eq,BitVec.setWidth_setWidth_of_le]
  all_goals try assumption
  all_goals have z : (0:BitVec 64).toNat=0 := rfl
  all_goals simp only [atom20,z,cmpSpec_CF,decide_eq_true_eq,BitVec.toNat_zero,headZero,BitVec.sub_self,
    BitVec.zero_ushiftRight,BitVec.setWidth_zero,BitVec.zero_and,Nat.mul_zero,noCopy,true_or] 
  all_goals first | assumption | exact Or.inl rfl | (apply LoadOk.of_region _ (Nat.le_refl _) (Nat.le_refl _); assumption) |
    (rw [show memLoad mem fr.rsp 64=fr.ret by assumption]; assumption)

def emptyFn := leafSpec () Fn102dc0.active emptyCore () ()

theorem emptyCorrect : emptyFn.Correct :=
  provedCallee () Fn102dc0.active emptyCore () rfl () rfl (fun _ => rfl) emptyBlocks (.done rfl)

@[refine_layout] def copyOut (len : Nat) (data : BitVec (8*len)) : Callee where
  entry := .l102dc0
  abi := Fn102dc0.active .l102dc0
  pre fr := [.fact (fr.rdx.toNat=len),.mem fr.rsi (8*len) data,.readable fr.rsi len,
    .fact (0<len → fr.rsi.toNat+len≤fr.rdi.toNat ∨ fr.rdi.toNat+len≤fr.rsi.toNat),
    .fact (0<len → fr.rdi.toNat+len≤0x102dc0 ∨ 0x102def≤fr.rdi.toNat),
    .fact (0<len → fr.rdi.toNat+len≤fr.rsp.toNat ∨ fr.rsp.toNat+8≤fr.rdi.toNat)] ++
    (if len=0 then [] else [.writable fr.rdi len])
  post fr := [.mem fr.rdi (8*len) data]
  writes fr := [⟨fr.rdi.toNat,len⟩]

private theorem oneBits {n} (a b : BitVec n) (h : n=0) : a=b := by subst n; exact Subsingleton.elim _ _

theorem copyOutCorrect (len : Nat) (data : BitVec (8*len)) : (copyOut len data).Correct := by
  intro fr a hl hat hf
  obtain ⟨abi,pre⟩ := (Atom.all_append _ _).1 hat
  obtain ⟨base,wr⟩ := (Atom.all_append _ _).1 pre
  obtain ⟨sz,src,rd,sep,code,stk,_⟩ := base
  change fr.rdx.toNat=len at sz
  subst len
  by_cases pos : 0<fr.rdx.toNat
  · have w : Writable fnCode a.store fr.rdi fr.rdx.toNat := by
      change Atom.All _ _ _ (if fr.rdx.toNat=0 then [] else _) at wr
      rw [ite_eq_right (by omega)] at wr; exact wr.1
    obtain ⟨o,ex,tr,out,frame⟩ := copyFnCorrect {fr with original:=a.store} a hl
      ((Atom.all_append _ _).2 ⟨abi,rd,w,sep pos,code pos,stk pos,rfl,trivial⟩) (.refl _ _)
    obtain ⟨r,_,val,_⟩ := (Atom.all_append _ _).1 out
    exact ⟨o,ex,tr,(Atom.all_append _ _).2 ⟨r,val.trans src,trivial⟩,hf.trans frame (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩)⟩
  · have z : fr.rdx=0 := BitVec.eq_of_toNat_eq (by change fr.rdx.toNat=0; omega)
    obtain ⟨o,ex,tr,out,frame⟩ := emptyCorrect {fr with original:=a.store} a hl
      ((Atom.all_append _ _).2 ⟨abi,z,trivial⟩) (.refl _ _)
    refine ⟨o,ex,tr,(Atom.all_append _ _).2 ⟨((Atom.all_append _ _).1 out).1,?_,trivial⟩,hf.trans frame ?_⟩
    · change memLoad o.store fr.rdi (8*fr.rdx.toNat)=data
      have width : 8*fr.rdx.toNat=0 := by rw [z]; rfl
      exact oneBits _ _ width
    · change RegionsWithin [fr.region] (fr.region :: _)
      simp only [RegionsWithin,List.mem_singleton,forall_eq]
      exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
