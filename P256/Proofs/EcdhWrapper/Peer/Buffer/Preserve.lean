import P256.Proofs.EcdhWrapper.Peer.Buffer.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {s t : RamState} {base : BitVec 64}

theorem byte_preserved (ag : AgreesExcept (components base) s t) {i : Nat}
    (bound : i<512) (outside : i<48 ∨ 305≤i) :
    t.external[base+BitVec.ofNat 64 i]?=s.external[base+BitVec.ofNat 64 i]? := by
  apply ag.byte
  intro c hc cover
  simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals
    obtain ⟨j,hj,eq⟩ := cover
    have eq' := (BitVec.add_right_inj base).mp (by
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using eq)
    have hn := congrArg BitVec.toNat eq'
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.reduceToNat] at hn
    omega

theorem registers_preserved (ag : AgreesExcept (components base) s t) :
    CalleeSavedRegistersUnchanged s t := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ag.read (n := 64) (r := 3) (by simp [components])
  · exact ag.read (n := 64) (r := 5) (by simp [components])
  · exact ag.read (n := 64) (r := 12) (by simp [components])
  · exact ag.read (n := 64) (r := 13) (by simp [components])
  · exact ag.read (n := 64) (r := 14) (by simp [components])
  · exact ag.read (n := 64) (r := 15) (by simp [components])

theorem word_preserved {initial : RamState}
    (rsp : stackPtr s=stackPtr initial-504)
    (ag : AgreesExcept (components (stackPtr s)) s t) {off : Nat}
    (bound : off≤48 ∨ (464≤off ∧ off≤472)) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64=
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
  have pos : off≤504 := by omega
  have addr := address rsp (off := 504-off) (by omega)
  rw [Nat.sub_sub_self pos] at addr
  rw [←addr]
  apply memLoad_congr
  intro j hj
  change (t.external[(stackPtr s+BitVec.ofNat 64 (504-off))+BitVec.ofNat 64 j]?).getD 0=_
  rw [BitVec.add_assoc,←BitVec.ofNat_add,byte_preserved ag (by omega) (by omega)]
  rfl

end P256.Proofs.EcdhWrapper.Peer.Buffer
