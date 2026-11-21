import ChaCha20Poly1305.Proofs.Decrypt.WrapLeaf
import ChaCha20Poly1305.Proofs.Decrypt.DetachTag
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Decrypt

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Detached

@[refine_layout] def splitTag (fr : Activation) : Micro.Step where
  entry := .l10158b
  exit := .l101596
  pre := live fr ++ [.writable fr.rsp 32,.fact (16≤fr.r14.toNat),
    .fact (fr.rsp.toNat+32≤0x10158b ∨ 0x101596≤fr.rsp.toNat)]
  post := live fr ++ [.mem (fr.rsp+24) 64 fr.r14]
  writes := [slot fr.rsp 24 8]

@[refine_layout] def branch (fr : Activation) (good : Bool) : Micro.Step where
  entry := .l1015d4
  exit := if good then .l1015d8 else .l101611
  pre := live fr ++ [.low 0 8 (if good then 0 else 1)]
  post := live fr
  writes := []

@[refine_layout] def cut (n sp : BitVec 64) : Invoke.Edge where
  site := .l1015d8
  resume := .l1015e5
  callee := trimFn n
  before fr := live fr ++ space fr 8 ++ [.fact (fr.rsp=sp),.writable fr.rsp 32,.mem (fr.rsp+24) 64 n,
    .fact (fr.r13.toNat≤n.toNat),.fact (fr.rsp.toNat+32≤0x102020 ∨ 0x10202b≤fr.rsp.toNat)]
  after fr := live fr ++ [.mem (fr.rsp+24) 64 fr.r13]
  footprint := [slot sp 24 8]

@[refine_layout] def checkCap (fr : Activation) (n : BitVec 64) : Micro.Step where
  entry := .l1015e5
  exit := .l1015ed
  pre := live fr ++ [.readable (fr.rsp+8) 8,.mem (fr.rsp+8) 64 n,.fact (n.toNat<2^32)]
  post := live fr
  writes := []

@[refine_layout] def checkLen (fr : Activation) (n cap : BitVec 64) : Micro.Step where
  entry := .l1015ed
  exit := .l1015ff
  pre := live fr ++ [.readable (fr.rsp+168) 8,.mem (fr.rsp+168) 64 cap,.readable (fr.rsp+24) 8,
    .mem (fr.rsp+24) 64 n,.fact (n.toNat≤cap.toNat)]
  post := live fr ++ [.gpr 2 n]
  writes := []

@[refine_layout] def copySite (n src dest : BitVec 64) (data : BitVec (8*n.toNat)) : Invoke.Edge where
  site := .l1015ff
  resume := .l10160d
  callee := copyOut n.toNat data
  before fr := live fr ++ space fr 8 ++ [.gpr 2 n,.fact (fr.rbx=dest),.readable (fr.rsp+16) 8,.mem (fr.rsp+16) 64 src,
    .readable 0x2013a8 8,.mem 0x2013a8 64 0x102dc0,
    .fact (src.toNat+n.toNat≤fr.rsp.toNat-8 ∨ fr.rsp.toNat≤src.toNat)] ++
    (copyOut n.toNat data).pre {push fr with rdi:=dest,rsi:=src,rdx:=n}
  after fr := basic fr ++ [.mem dest (8*n.toNat) data]
  footprint := [⟨dest.toNat,n.toNat⟩]

@[refine_layout] def returnCore (good : Bool) : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => match good with | true => .l10160d | false => .l101611
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ _ _ => []
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done _ _ _ := [.gpr 0 (if good then 0 else 1)]
  footprint _ _ := []

@[refine_layout] def returnFn (good : Bool) := leafSpec () (fun _ => Decrypt.frameAt .l101616) (returnCore good) () ()

set_option maxHeartbeats 900000
set_option maxRecDepth 8000
set_option pp.maxSteps 180

theorem splitValid (fr : Activation) : Micro.Valid (splitTag fr) := by
  unfold Micro.Valid
  refine_one [Micro.program,splitTag,cmpSpec_CF]
  all_goals first | assumption | (exfalso; bv_omega)

theorem branchValid (fr : Activation) (good : Bool) : Micro.Valid (branch fr good) := by
  cases good <;> unfold Micro.Valid <;> refine_one [Micro.program,branch]
  all_goals first | assumption | contradiction | rfl

theorem cutValid (n sp : BitVec 64) : (Invoke.layout (cut n sp)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp
  refine_uir [Invoke.program]
  refine_lifted []
  prepare_call (fun m => ({fr with original:=m,rsp:=fr.rsp-8,ret:=0x1015e5,rdi:=fr.rsp+8,rsi:=fr.r13},()))
  · refine_close []
    all_goals try assumption
  · close_resume []
    all_goals first | assumption | (simp only [BitVec.add_assoc] at done11; exact done11)

theorem checkCapValid (fr : Activation) (n : BitVec 64) : Micro.Valid (checkCap fr n) := by
  unfold Micro.Valid
  refine_one [Micro.program,checkCap,cmpSpec_ZF]
  all_goals first | assumption | (exfalso; bv_omega)

theorem checkLenValid (fr : Activation) (n cap : BitVec 64) : Micro.Valid (checkLen fr n cap) := by
  unfold Micro.Valid
  refine_one [Micro.program,checkLen,cmpSpec_CF,cmpSpec_ZF]
  all_goals first | assumption | rfl | (exfalso; bv_omega)

attribute [local irreducible] memLoad memStore

theorem copySiteValid (n src dest : BitVec 64) (data : BitVec (8*n.toNat)) :
    (Invoke.layout (copySite n src dest data)).BlockSimulation fnCode .site := by
  by_cases h : n.toNat=0
  all_goals
    refine_intro
    subst dest
    refine_uir [Invoke.program]
    refine_lifted []
    prepare_call (fun m => ({fr with original:=m,rsp:=fr.rsp-8,ret:=0x10160d,rdi:=fr.rbx,rsi:=src,rdx:=n},()))
    · refine_close [h]
      all_goals try (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_toNat (by bv_omega) (by bv_omega) (by bv_omega))]; exact atom25)
      all_goals simp [h,Atom.All,Atom.Holds] at atom31 ⊢
      all_goals first | assumption | (apply atom31.of_frame; apply (RamWriteFrame.refl _ [⟨(fr.rsp-8).toNat,8⟩]).memStore; simp [InRegions,InRegion]; bv_omega)
    · close_resume [h]
      all_goals try assumption

theorem returnCorrect (good : Bool) : (returnFn good).Correct := by
  apply provedCallee () (fun _ => Decrypt.frameAt .l101616) (returnCore good) () rfl () rfl (fun _ => rfl) _ (.done rfl)
  intro l; cases l; cases good <;> x86_refine [Copy.program]

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
