import ChaCha20Poly1305.Proofs.Decrypt.HashCall
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

structure Raw where
  k : Vector (BitVec 64) 4
  nl : BitVec 64
  nh : BitVec 32

inductive Point | entry | second | keygen

def program : Program (fun _ => _root_.Empty) Point (fun _ => 0) 0 := ⟨fun
  | .entry => .terminate (.br ⟨.second,#v[]⟩)
  | .second => .terminate (.br ⟨.keygen,#v[]⟩)
  | .keygen => .terminate (.ret #v[])⟩

@[refine_layout] def srcGeo (fr : Activation) : List Atom :=
  [.readable fr.rdi 32,.readable fr.rsi 12,
   .fact (fr.rsp.toNat≤0x1001f0 ∨ 0x102def+864≤fr.rsp.toNat),
   .fact (fr.rdi.toNat+32≤fr.rsp.toNat-440 ∨ fr.rsp.toNat≤fr.rdi.toNat),
   .fact (fr.rsi.toNat+12≤fr.rsp.toNat-440 ∨ fr.rsp.toNat≤fr.rsi.toNat)]

@[refine_layout] def inputs (x : Raw) (fr : Activation) : List Atom :=
  [.mem fr.rdi 64 x.k[0],.mem (fr.rdi+8) 64 x.k[1],.mem (fr.rdi+16) 64 x.k[2],.mem (fr.rdi+24) 64 x.k[3],
   .mem fr.rsi 64 x.nl,.mem (fr.rsi+8) 32 x.nh]

@[refine_layout] def constQ (sp : BitVec 64) : List Atom :=
  [.mem (sp+208) 64 3684054920433006693,.mem (sp+216) 64 7719281312240119090]

@[refine_layout] def beginWords (x : Raw) (sp : BitVec 64) : List Atom :=
  constQ sp ++ [.mem (sp+224) 64 x.k[0],.gpr 0 x.k[1],.mem (sp+64) 64 x.k[2],.mem (sp+72) 64 x.k[3],
    .mem (sp+84) 64 x.nl,.mem (sp+92) 32 x.nh]

@[refine_layout] def preCore (x : Raw) : LayoutCore program Empty.semantics lifted Unit where
  start | .entry => .l1001f0 | .second => .l10024c | .keygen => .l1002e5
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l _ fr _ := srcGeo fr ++ match l with
    | .entry => inputs x fr
    | .second => constQ (fr.rsp-440) ++ [.mem (fr.rsp-440+224) 64 x.k[0],.mem (fr.rsp-440+232) 64 x.k[1],
      .gpr 0 x.k[2],.mem (fr.rdi+24) 64 x.k[3],.mem fr.rsi 64 x.nl,.mem (fr.rsi+8) 32 x.nh]
    | .keygen => beginWords x (fr.rsp-440)
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ _ => []
  footprint := fun _ _ => []

abbrev preLayout (x : Raw) := Layout.withFrame Fn1001f0.frameAt Fn1001f0.doneAt (preCore x)

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option pp.maxSteps 130

theorem entry0 (x : Raw) : (preLayout x).BlockSimulation fnCode .entry := by
  x86_refine [program]
  all_goals try assumption

theorem entry1 (x : Raw) : (preLayout x).BlockSimulation fnCode .second := by
  x86_refine [program]
  all_goals try assumption
  all_goals first
    | (rw [show fr.rsp-232=fr.rsp-440+208 by bv_omega]; assumption)
    | (rw [show fr.rsp-224=fr.rsp-440+216 by bv_omega]; assumption)
    | (rw [show fr.rsp-216=fr.rsp-440+224 by bv_omega]; assumption)
    | (rw [show fr.rsp-208=fr.rsp-440+232 by bv_omega]; assumption)


theorem beginKey (x : Raw) {fr a} (h : (preLayout x).Rel fnCode (fr,()) (unitLoc .entry) a) :
    Ahead lifted fnCode ((preLayout x).Rel fnCode (fr,()) (unitLoc .keygen)) a := by
  apply aheadBind (segment (preLayout x) (j := .second) (entry0 x) rfl h)
  intro _ hm
  exact segment (preLayout x) (j := .keygen) (entry1 x) rfl hm

end ChaCha20Poly1305.Proofs.Decrypt.Detached
