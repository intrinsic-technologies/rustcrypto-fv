import Sha2.Proofs.Common.SHA256.Initialize.Proof.Words
import Sha2.Proofs.Common.SHA256.Initialize.Proof.ClearSemantics
import Sha2.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

set_option maxHeartbeats 1000000 in
theorem correct [Bindings] (boundary : ReturnBoundary) (l : Layout v)
    (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram l.start l.bytes.length) : Contract boundary l := by
  intro base s ready code pre
  obtain ⟨fuel, t, run, readyT, codeT, rip, frame, packed, constants⟩ :=
    words_run boundary l outside inside base s ready code pre 4 (Nat.le_refl _)
  have counterAddress : l.clear.counter.read t = base + 96 := by
    rw [Address.read_eq (l.prefix_register frame _ (fun j _ hj =>
      pre.valid.independentCounter j hj)), pre.counter]
  have tailAddress : l.clear.tail.read t = base + 63 := by
    rw [Address.read_eq (l.prefix_register frame _ (fun j _ hj =>
      pre.valid.independentTail j hj)), pre.tail]
  have clearPre : l.clear.Pre (l.wordPC 4) t := by
    refine ⟨rip, pre.clear.counterValid, pre.clear.tailValid, pre.clear.tailRexX,
      pre.clear.tailRexB, ?_, ?_, ?_, ?_, ?_⟩
    · rw [counterAddress, ← pre.counter]
      exact ⟨⟨pre.clear.counterWritable.low, fun a ha =>
        frame.grow _ (pre.clear.counterWritable.mem a ha)⟩, pre.clear.counterWritable.tables⟩
    · rw [counterAddress, ← pre.counter]
      exact pre.clear.counterApart
    · rw [tailAddress, ← pre.tail]
      exact ⟨pre.clear.tailWritable.low, fun a ha => frame.grow _ (pre.clear.tailWritable.mem a ha),
        pre.clear.tailWritable.tables⟩
    · rw [tailAddress, ← pre.tail]
      exact pre.clear.tailApart
    · rw [counterAddress, tailAddress, ← pre.counter, ← pre.tail]
      exact pre.clear.separate
  have insideClear : BlockInProgram (l.wordPC 4) l.clear.bytes.length := by
    intro a ha
    change InProgram (l.start + BitVec.ofNat 64 (l.offset 4) + BitVec.ofNat 64 a)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply inside
    have := l.offset_clear
    omega
  obtain ⟨count, u, step, readyU, _, result⟩ :=
    Clear.run boundary (l.wordPC 4) l.clear outside insideClear
      t readyT (l.clearCode codeT) clearPre
  have codeU : CodeIn (codeRange l.start l.bytes) u := result.codeIn (by
    apply Clear.avoids
    · rw [counterAddress]
      intro i hi j hj equal
      apply pre.codeApart (96 + i) (by omega) j hj
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using equal
    · rw [tailAddress]
      intro i hi j hj equal
      apply pre.codeApart (63 + i) (by omega) j hj
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using equal) codeT
  have packedU (j : Fin 4) :
      memLoad u.external (base + 64 + BitVec.ofNat 64 (8 * (l.words[j]).index.val)) 64 =
        packedWord (l.words[j]).index v := by
    rw [Clear.mem_unchanged result _ ?_ ?_]
    · exact packed j j.isLt
    · rw [counterAddress]
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      change RangeApart (base + BitVec.ofNat 64 96) 8
        (base + BitVec.ofNat 64 (64 + 8 * (l.words[j]).index.val)) 8
      apply RangeApart.offsets
      · decide
      · have := (l.words[j]).index.isLt; omega
      · right; have := (l.words[j]).index.isLt; omega
    · rw [tailAddress]
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      change RangeApart (base + BitVec.ofNat 64 63) 1
        (base + BitVec.ofNat 64 (64 + 8 * (l.words[j]).index.val)) 8
      apply RangeApart.offsets
      · decide
      · have := (l.words[j]).index.isLt; omega
      · left; omega
  have totalFrame : AgreesExcept (l.components base) s u := by
    apply (frame.trans result.agrees).mono
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with h | h
    · simp only [Layout.prefixComponents, l.prefix_all, Layout.components,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | rfl | rfl
      · exact Or.inl h
      · simp
      · simp
    · simp [Clear.effect, Effect.components, counterAddress, tailAddress] at h
      rcases h with rfl | rfl | rfl <;> simp [Layout.components]
  have readable : MemReadable u base 104 :=
    ⟨pre.baseReadable.low, fun i hi => totalFrame.grow _ (pre.baseReadable.mem i hi)⟩
  have hash : HashStateAt u (base + 64) v.initialHash := by
    apply HashStateAt.initial_of_packed v
    · intro j hj
      let k : Fin 4 := ⟨3-j, by omega⟩
      have index : (l.words[k]).index.val = j := by
        have := pre.valid.order k
        change (l.words[k]).index.val = 3 - (3-j) at this
        omega
      have word := packedU k
      rw [packedWord_eq, index] at word
      exact word
    · exact Common.Memory.memReadable_sub readable 64 32 (by decide)
  have tail : u.external[base + 63]? = some 0 := by
    have value : memLoad u.external (base + 63) 8 = 0 := by
      have writes := result.writes
      change memLoad u.external (l.clear.counter.read t) 64 = 0 ∧
        memLoad u.external (l.clear.tail.read t) 8 = 0 at writes
      exact tailAddress ▸ writes.2
    have bytes := Bytes.of_memLoad (a := base + 63) (n := 8)
      (m := u.external) (fun i hi => by
        have read := Common.Memory.memReadable_sub readable 63 1 (by decide)
        exact read.mem i hi)
    rw [value] at bytes
    simpa [storedByte] using bytes 0 (by decide)
  have counter : memLoad u.external (base + 96) 64 = 0 := by
    have writes := result.writes
    change memLoad u.external (l.clear.counter.read t) 64 = 0 ∧
      memLoad u.external (l.clear.tail.read t) 8 = 0 at writes
    exact counterAddress ▸ writes.1
  have finalConstant (i : Fin 4) (loading : (l.words[i]).loadConstant = true)
      (last : ∀ j : Fin 4, i.val < j.val → (l.words[j]).loadConstant = true →
        (l.words[j]).register ≠ (l.words[i]).register) :
      (.reg ((l.words[i]).register.setWidth 5) : Operand 64).read u =
        packedWord (l.words[i]).index v := by
    have unchanged : (.reg ((l.words[i]).register.setWidth 5) : Operand 64).read u =
        (.reg ((l.words[i]).register.setWidth 5) : Operand 64).read t := by
      apply result.agrees.read
      simp [Clear.effect, Effect.components]
    rw [unchanged]
    exact constants i i.isLt loading (fun j after _ loaded => last j after loaded)
  refine ⟨fuel + count, u, run.trans step, readyU, codeU,
    result.rip.trans l.clear_finish, HasherAt.empty hash tail counter, ?_,
    totalFrame, finalConstant⟩
  change (.reg 4 : Operand 64).read u = (.reg 4 : Operand 64).read s
  apply totalFrame.read
  simp only [Layout.components, List.mem_append, List.mem_map, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_false, not_exists, not_and]
  intro b ⟨member, loading⟩ equal
  obtain ⟨j, _, rfl⟩ := l.prefix_member (i := 4) (l.prefix_all.symm ▸ member)
  exact register_ne (pre.valid.independentStack j loading) (Component.reg.inj equal)

end Sha2.Proofs.Common.SHA256.Initialize
