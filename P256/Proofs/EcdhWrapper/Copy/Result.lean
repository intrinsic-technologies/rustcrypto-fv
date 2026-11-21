import P256.Proofs.EcdhWrapper.Copy.Run
import P256.Proofs.EcdhWrapper.Copy.Chunks

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.EcdhWrapper.Copy
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (copyComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [copyComponents]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s + 112) 32, by simp [copyComponents], ?_⟩
    · exact ⟨2+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨i, by omega, by simp [stackPtr, Operand.read_reg64, gprIndex]⟩
    · exact ⟨7+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨15+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨23+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨31+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨3+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem hasBytes {s t : RamState} {input : ByteArray}
    (pre : CopyPre input s .rax 0x10683d) (h : (effect s).Holds s t) :
    (MemoryRegion.mk (stackPtr s + 112).toNat 32).HasBytes t.external input := by
  obtain ⟨_, _, _, h2, h0, h7, h15, h23, h31, h3⟩ := h.writes
  exact chunks_hasBytes pre (frame h).grow h2 h0 h7 h15 h23 h31 h3

end P256.Proofs.EcdhWrapper.Copy
