import K256.Proofs.Signing.Composition.Wrapper.State
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Sec1.Parser.Result.Copy

namespace K256.Proofs.Signing.Composition.Wrapper.Install

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Prepare
open K256.Proofs.Signing.LIR

abbrev storeWord (m : Ram) (q : BitVec 64) (off : Nat) (v : BitVec 64) : Ram :=
  memStore m (q + BitVec.ofNat 64 off) v

def staged (q : BitVec 64) (m : Ram) (words : Vector (BitVec 64) 4) : Ram :=
  storeWord (storeWord (storeWord (storeWord m q 320 words[0]) q 328 words[1]) q 336 words[2]) q 344 words[3]

def cleared (q : BitVec 64) (m : Ram) : Ram :=
  storeWord (storeWord (storeWord (storeWord m q 200 0) q 208 0) q 216 0) q 224 0

def scratch (q : BitVec 64) (m : Ram) : Ram :=
  storeWord (storeWord (storeWord (storeWord m q 0 0) q 8 0) q 16 0) q 24 0

def copied (q : BitVec 64) (m : Ram) : Ram :=
  memCopy (memCopy m (q+80) (q+320) 120) (q+200) (q+80) 120

def finished (q msg len : BitVec 64) (m : Ram) : Ram :=
  memStore (storeWord (storeWord m q 320 msg) q 328 len) (q-8) (0x102795 : BitVec 64)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1700000 in
theorem finishBlock {a : Registers} {m : Ram} {q msg len : BitVec 64}
    {words : Vector (BitVec 64) 4}
    (win : Writable Extracted.programImage m (q-8) 480)
    (high : q.toNat + 472 < 2^32) (room : 8 ≤ q.toNat)
    (rsp : a[4].get 64 = q) (df : a[22].get 1 = 0)
    (message : a[15].get 64 = msg) (length : a[14].get 64 = len)
    (word0 : memLoad m (q+40) 64 = words[0])
    (word1 : memLoad m (q+48) 64 = words[1])
    (word2 : memLoad m (q+56) 64 = words[2])
    (word3 : memLoad m (q+64) 64 = words[3]) :
    let n := finished q msg len (copied q (scratch q (cleared q (staged q m words))))
    ∃ (b : Registers), program.runBlock (dialect Extracted.programImage) ⟨.l1026a6,a,m⟩ =
      .call ⟨.l105420,b,n⟩ (resume .l102795 0x102795) ∧
      b[4] = ⟨64,q-8⟩ ∧ b[7] = ⟨64,q+72⟩ ∧ b[6] = ⟨64,q+200⟩ ∧
      b[2] = ⟨64,q+320⟩ ∧ b[1] = ⟨64,1⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  dsimp only [finished,copied,scratch,cleared,staged,storeWord]
  refine Exists.intro (α := Registers) ?newRegs ?_
  rotate_left
  refine And.intro ?run ?_
  case run =>
    cfg_eval [rsp, df, message, length, word0, word1, word2, word3]
    segment_words [word0, word1, word2, word3]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first
      | slot_guard using code_l1026a6
      | rep_copy_guard using code_l1026a6
      | (dsimp only [memCopy]; slot_guard using code_l1026a6))
    rfl
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  rintro ⟨i,_⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Signing.Composition.Wrapper.Install
