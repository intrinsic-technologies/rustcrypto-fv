import ChaCha20Poly1305.Proofs.Decrypt.PadScope

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def lead : Bool → Lifted.Label | false => .l100417 | true => .l10049a
@[refine_layout] def enter (ct full : Bool) := match full with | true => lead ct | false => finish ct
@[refine_layout] def maskLow (n : BitVec 64) := (n.setWidth 32 &&& 15).setWidth 64
@[refine_layout] def maskA (n : BitVec 64) := (9223372036854775792#64) &&& n
@[refine_layout] def maskC (n : BitVec 64) := (274877906928#64) &&& n
@[refine_layout] def aadRegs (fr : Activation) (n : BitVec 64) := {fr with r13 := maskA n,r14 := maskLow n}
@[refine_layout] def ctRegs (fr : Activation) (n ptr : BitVec 64) := {fr with r15 := maskC n,r13 := ptr,r14 := maskLow n}
@[refine_layout] def slots (fr : Activation) (n : BitVec 64) : List Atom :=
  [.mem (fr.rsp+8) 64 fr.r13,.mem (fr.rsp+16) 64 fr.rbx,.mem (fr.rsp+192) 64 n,.mem (fr.rsp+200) 64 fr.r14]

@[refine_layout] def setupA (fr : Activation) (n : BitVec 64) (full : Bool) : Micro.Step where
  entry := .l1003e3
  exit := enter false full
  pre := regs fr ++ [.gpr 5 n,.writable fr.rsp 208,
    .fact (fr.rsp.toNat+208 ≤ 0x1003e3 ∨ 0x100417 ≤ fr.rsp.toNat)]
  post := regs (aadRegs fr n) ++ slots fr n
  writes := [⟨fr.rsp.toNat+8,16⟩,⟨fr.rsp.toNat+192,16⟩]

@[refine_layout] def setupC (fr : Activation) (n ptr vec : BitVec 64) (full : Bool) : Micro.Step where
  entry := .l100479
  exit := enter true full
  pre := regs fr ++ [.readable fr.rsp 32,.mem (fr.rsp+16) 64 vec,.readable vec 8,.mem vec 64 ptr,.mem (fr.rsp+24) 64 n,
     .fact (fr.r15=274877906879)]
  post := regs (ctRegs fr n ptr)
  writes := []

@[refine_layout] def beginRegs (ct : Bool) (fr : Activation) := match ct with
  | true => {fr with rbx := fr.r15} | false => {fr with rbx := fr.r13}
@[refine_layout] def beginStep (ct : Bool) (fr : Activation) (src : BitVec 64) : Micro.Step where
  entry := lead ct
  exit := site ct
  pre := regs fr ++ match ct with
    | true => [.fact (fr.r13=src)] | false => [.readable (fr.rsp+8) 8,.mem (fr.rsp+8) 64 src]
  post := regs (beginRegs ct fr) ++ [.gpr 6 src]
  writes := []

@[refine_layout] def nextLabel (ct pad : Bool) := match ct,pad with
  | false,false => Lifted.Label.l100479 | false,true => .l10043a
  | true,false => .l1004fc | true,true => .l1004c2

@[refine_layout] def bpAtoms (ct : Bool) (v : BitVec 64) : List Atom := match ct with
  | true => [.gpr 5 v] | false => []

@[refine_layout] def testStep (ct pad : Bool) (fr : Activation) (tag : BitVec 64) : Micro.Step where
  entry := finish ct
  exit := nextLabel ct pad
  pre := regs fr ++ match ct with
    | true => [.readable (fr.rsp+448) 8,.mem (fr.rsp+448) 64 tag] | false => []
  post := regs fr ++ bpAtoms ct tag
  writes := []

set_option maxHeartbeats 600000
set_option maxRecDepth 6000
set_option pp.maxSteps 130

theorem setupAValid (fr : Activation) (n : BitVec 64) (full : Bool) (cond : 16 ≤ n.toNat ↔ full=true) : Micro.Valid (setupA fr n full) := by
  cases full <;> simp at cond
  all_goals unfold Micro.Valid
  all_goals refine_one [Micro.program,setupA]
  all_goals try assumption
  all_goals try (exfalso; simp only [cmpSpec_CF,decide_eq_true_eq,Bool.not_eq_true] at hc; bv_omega)

theorem setupCValid (fr : Activation) (n ptr vec : BitVec 64) (full : Bool) (cond : 16 ≤ n.toNat ↔ full=true) : Micro.Valid (setupC fr n ptr vec full) := by
  cases full <;> simp at cond
  all_goals unfold Micro.Valid
  all_goals refine_one [Micro.program,setupC]
  all_goals try assumption
  all_goals try rfl
  all_goals try (exfalso; simp only [cmpSpec_CF,decide_eq_true_eq,Bool.not_eq_true] at hc; bv_omega)

theorem beginValid (ct : Bool) (fr : Activation) (src : BitVec 64) : Micro.Valid (beginStep ct fr src) := by
  cases ct <;> unfold Micro.Valid <;> refine_one [Micro.program,beginStep]
  all_goals first | rfl | assumption | (subst src; rfl)

theorem testValid (ct pad : Bool) (fr : Activation) (tag : BitVec 64) (cond : fr.r14≠0 ↔ pad=true) : Micro.Valid (testStep ct pad fr tag) := by
  cases ct <;> cases pad <;> simp at cond
  all_goals unfold Micro.Valid
  all_goals refine_one [Micro.program,testStep]
  all_goals first | assumption | rfl | contradiction

end ChaCha20Poly1305.Proofs.Decrypt.Hash
