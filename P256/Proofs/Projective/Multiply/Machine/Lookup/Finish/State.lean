import P256.Proofs.Projective.Multiply.Machine.Lookup.State
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Run
import P256.Proofs.Projective.Multiply.Machine.Lookup.Call.Binary

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure NegatedState [Bindings] (s t : RamState) (point : Projective) (negative : Bool)  : Prop extends FrameState s t where
  rip : t.RIP = 0x1048f1
  value : ProjectiveAt t (stackPtr s - 344) point
  negated : ProjectiveAt t (stackPtr s - 144) point.negate
  rbp : t.regValue .rbp = if negative then 1 else 0
  r14 : t.regValue .r14 = stackPtr s - 344
  r15 : t.regValue .r15 = stackPtr s - 112
  rbx : t.regValue .rbx = stackPtr s - 80
  output : (Operand.mem (stackPtr s - 152) : Operand 64).read t = s.regValue .rdi

structure SelectedState [Bindings] (s t : RamState) (point : Projective)  : Prop extends FrameState s t where
  rip : t.RIP = 0x10494b
  value : ProjectiveAt t (stackPtr s - 344) point
  r14 : t.regValue .r14 = stackPtr s - 344
  output : (Operand.mem (stackPtr s - 152) : Operand 64).read t = s.regValue .rdi

theorem copy_bytes {s t u : RamState} {dst offset len : Nat}
    (agr : AgreesExcept [.reg 0,.reg 1,.mem (stackPtr s-BitVec.ofNat 64 dst) 32,.rip] t u)
    (apart : OffsetsApart (-BitVec.ofNat 64 dst) 32 (-BitVec.ofNat 64 offset) len)
    (small : len + 32 < 2^64) :
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply agr.byte
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact id
  rintro ⟨j,hj,he⟩
  apply OffsetsApart.ne apart (stackPtr s) hj hi (by omega)
  simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem select_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {select : Bool}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (site : BinaryCallSite 0x114380 128)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) x)
    (hy : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.rightOffset) y)
    (choice : t.regValue .rcx = if select then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 site.layout.outputOffset) (if select then y else x) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 360 → len ≤ offset + 8 →
        (offset + 32 ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  exact binary_call (op := fun x y => if select then y else x) pre state site
    (fun v hp hc hx hy => Select.field_select_correct hp hx hy (hc.trans choice))
    rip input right output hx hy

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
