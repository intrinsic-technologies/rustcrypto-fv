import P256.Proofs.Projective.Multiply.Machine.Lookup.Selection
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Run

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def roundOffset : Nat → Nat
  | 0 => 0x44ed
  | 1 => 0x4550
  | 2 => 0x45ba
  | 3 => 0x4622
  | 4 => 0x468a
  | 5 => 0x46f2
  | 6 => 0x475a
  | 7 => 0x47c2
  | _ => 0x482d

structure RoundState [Bindings] (s t : RamState) (table : Fin 8 → Projective)
    (digit : BitVec 8) (index : Nat) : Prop extends FrameState s t where
  rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (roundOffset index)
  value : ProjectiveAt t (stackPtr s - 344) (scanPrefix table (digitMagnitude digit) index)
  magnitude : (t.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit)
  r13 : index < 8 → t.regValue .r13 = s.regValue .rsi
  rbp : t.regValue .rbp = stackPtr s - (if index < 2 then 344 else 280)
  r14 : t.regValue .r14 = stackPtr s - (if index = 0 then 216 else 344)
  r12 : 0 < index → t.regValue .r12 = stackPtr s - 248
  digit : (Operand.mem (stackPtr s - 348) : Operand 32).read t = (s.regValue .rdx).setWidth 32
  output : (Operand.mem (stackPtr s - 152) : Operand 64).read t = s.regValue .rdi

theorem digit_choice (digit : BitVec 8) (index : Fin 8) :
    ((if BitVec.ofNat 8 (digitMagnitude digit) = BitVec.ofNat 8 (index.val+1)
      then 1 else 0) : BitVec 64) =
      if decide (digitMagnitude digit = index.val+1) then 1 else 0 := by
  have h : BitVec.ofNat 8 (digitMagnitude digit) = BitVec.ofNat 8 (index.val+1) ↔
      digitMagnitude digit = index.val+1 := by
    have e := magnitude_eq digit index
    have he := congrArg (fun b : Bool => b = true) e
    simpa only [beq_iff_eq, decide_eq_true_eq] using Iff.of_eq he
  simp [h]

theorem selected_point {t : RamState} {address : BitVec 64} {p q : Projective} {select : Bool}
    (x : MontgomeryAt t address (if select then q.x else p.x))
    (y : MontgomeryAt t (address+32) (if select then q.y else p.y))
    (z : MontgomeryAt t (address+64) (if select then q.z else p.z)) :
    ProjectiveAt t address (if select then q else p) := by
  cases select <;> exact ⟨x,y,z⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
