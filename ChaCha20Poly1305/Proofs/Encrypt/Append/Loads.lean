import ChaCha20Poly1305.Proofs.Encrypt.Append.Prologue

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

theorem append_descriptor_word [Bindings] {s t : RamState} {buffer value : BitVec 64}
    {length offset : Nat} {tag : Vector UInt8 16}
    (pre : AppendPre s buffer length tag)
    (frame : MemoryWriteFrame s t #v[Stack.region s 48]) (hoff : offset + 8 ≤ 24)
    (word : (⟨(s.regValue .rdi).toNat + offset, 8⟩ : MemoryRegion).Word64At
      s.external value) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 offset) 8 ∧
      wd t (s.regValue .rdi + BitVec.ofNat 64 offset) = value := by
  have hb : (s.regValue .rdi).toNat + 24 < 2 ^ 32 := pre.descriptor.1
  have hd : (appendDescriptor s).Disjoint (Stack.region s 48) :=
    (List.pairwise_cons.mp pre.separation.1).1 _ (by simp)
  have addr : BitVec.ofNat 64 ((s.regValue .rdi).toNat + offset) =
      s.regValue .rdi + BitVec.ofNat 64 offset := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have keep : ∀ i < 8,
      t.external[s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame
    intro r hr
    have he : r = Stack.region s 48 := by simpa using hr
    subst r
    apply hd
    change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + 24
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · intro i hi
    rw [keep i hi]
    have h := loadBytes_isSome word.2 i hi
    simpa only [addr] using h
  · have initial := word64At_memLoad word
    change memLoad t.external _ 64 = value
    rw [← initial, addr]
    apply memLoad_congr
    intro i hi
    change i < 8 at hi
    simp only [memByte]
    congr 1
    exact keep i hi

end ChaCha20Poly1305.Proofs.Encrypt
