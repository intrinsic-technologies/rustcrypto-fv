import K256.Proofs.ParseSignature.Fill.Blocks

namespace K256.Proofs.ParseSignature.Fill

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.LIR

def stackWindow (fr : Activation) : MemoryRegion := buffer (fr.rsp - 80) 80

def loopStack (fr : Activation) : MemoryRegion := buffer (fr.rsp - 80) 32

def fillWrites (fr : Activation) : List MemoryRegion := [stackWindow fr, buffer fr.rdx 32]

def loopWrites (fr : Activation) : List MemoryRegion := [loopStack fr, buffer fr.rdx 32]

structure MemoryPre (code : CodeMap) (fr : Activation) : Prop where
  input : Readable fr.original fr.rdi 32
  output : Writable code fr.original fr.rdx 32
  retReadable : Readable fr.original fr.rsp 8
  stackWritable : Writable code fr.original (fr.rsp - 208) 208
  stackRoom : fr.low.toNat + 208 ≤ fr.rsp.toNat
  stackAlign : fr.rsp.toNat % 16 = 8
  gotReadable : Readable fr.original 0x203dd0 8
  gotValue : memLoad fr.original 0x203dd0 64 = 0x12a820
  gotStack : 0x203ef8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0
  gotOutput : Outside [buffer fr.rdx 32] 0x203dd0 8
  inputStack : Outside [callStack fr] fr.rdi 32
  inputOutput : Outside [buffer fr.rdx 32] fr.rdi 32
  outputStack : Outside [callStack fr] fr.rdx 32

variable {code : CodeMap} {fr : Activation}

theorem MemoryPre.stackNat (h : MemoryPre code fr) {d : Nat} (hd : d ≤ 208) :
    (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
  have room := h.stackRoom
  rw [BitVec.toNat_sub_of_le]
  · change fr.rsp.toNat - d % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  · change d % 2^64 ≤ fr.rsp.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem MemoryPre.stackWord (h : MemoryPre code fr) {m : Ram} {d : Nat}
    (hd : 8 ≤ d ∧ d ≤ 208) (hf : RamWriteFrame fr.original m (fillWrites fr)) :
    Writable code m (fr.rsp - BitVec.ofNat 64 d) 8 := by
  have room := h.stackRoom
  have h208 : (fr.rsp - 208).toNat = fr.rsp.toNat - 208 := h.stackNat (by decide : 208 ≤ 208)
  apply (h.stackWritable.of_frame hf).sub <;> rw [h208, h.stackNat hd.2] <;> omega

theorem MemoryPre.stackInWindow (h : MemoryPre code fr) {d : Nat}
    (hd : 8 ≤ d ∧ d ≤ 80) : InRegion (stackWindow fr) (fr.rsp - BitVec.ofNat 64 d) 8 := by
  have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
  have room := h.stackRoom
  have low := h.retReadable.low
  simp only [InRegion, stackWindow, buffer, sp80, h.stackNat (by omega : d ≤ 208)]
  omega

theorem MemoryPre.stackInLoop (h : MemoryPre code fr) {d : Nat}
    (hd : 56 ≤ d ∧ d ≤ 80) : InRegion (loopStack fr) (fr.rsp - BitVec.ofNat 64 d) 8 := by
  have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
  have room := h.stackRoom
  have low := h.retReadable.low
  simp only [InRegion, loopStack, buffer, sp80, h.stackNat (by omega : d ≤ 208)]
  omega

theorem loopWithinWindow (fr : Activation) :
    RegionsWithin (loopWrites fr) (fillWrites fr) := by
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨stackWindow fr, List.mem_cons_self .., Nat.le_refl _, Nat.add_le_add_left (by decide : 32 ≤ 80) _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩

theorem MemoryPre.writesWithin (h : MemoryPre code fr) :
    RegionsWithin (fillWrites fr) (fr.region :: [buffer fr.rdx 32]) := by
  intro r hr
  simp only [fillWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
    have room := h.stackRoom
    refine ⟨fr.region, List.mem_cons_self .., ?_, ?_⟩
    all_goals simp only [stackWindow, buffer, Activation.region, sp80] <;> omega
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩

theorem MemoryPre.gotOutside (h : MemoryPre code fr) :
    Outside (fillWrites fr) 0x203dd0 8 := by
  refine ⟨by decide, ?_⟩
  intro r hr
  simp only [fillWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
    have room := h.stackRoom
    have sep := h.gotStack
    change 0x203dd8 ≤ (fr.rsp - 80).toNat ∨ (fr.rsp - 80).toNat + 80 ≤ 0x203dd0
    rw [sp80]
    omega
  · exact h.gotOutput.2 _ (List.mem_cons_self ..)

theorem MemoryPre.inputOutside (h : MemoryPre code fr) :
    Outside (fillWrites fr) fr.rdi 32 := by
  refine ⟨h.inputStack.1, ?_⟩
  intro r hr
  simp only [fillWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
    have sep := h.inputStack.2 _ (List.mem_cons_self ..)
    have room := h.stackRoom
    change fr.rdi.toNat + 32 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at sep
    simp only [stackWindow, buffer, sp80]
    omega
  · exact h.inputOutput.2 _ (List.mem_cons_self ..)

theorem outsideSubset {rs : List MemoryRegion} {b a : BitVec 64} {n k : Nat}
    (h : Outside rs b n) (h₁ : b.toNat ≤ a.toNat) (h₂ : a.toNat + k ≤ b.toNat + n) :
    Outside rs a k := by
  refine ⟨by have := h.1; omega, ?_⟩
  intro r hr
  obtain sep | sep := h.2 r hr
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem wordOffsetNat {b : BitVec 64} (hb : b.toNat + 32 ≤ 2^32) {off : Nat}
    (ho : off + 8 ≤ 32) : (b + BitVec.ofNat 64 off).toNat = b.toNat + off := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem MemoryPre.outputIn (h : MemoryPre code fr) {i : Nat} (hi : i < 4) :
    InRegion (buffer fr.rdx 32) (wordAddr fr.rdx 64 i) 8 := by
  have hj : 8 * i + 8 ≤ 32 := by omega
  have eq := wordOffsetNat h.output.readable.low hj
  have low := h.output.readable.low
  change fr.rdx.toNat ≤ (fr.rdx + BitVec.ofNat 64 (8 * i)).toNat ∧
    (fr.rdx + BitVec.ofNat 64 (8 * i)).toNat + 8 ≤ fr.rdx.toNat + 32 ∧
    (fr.rdx + BitVec.ofNat 64 (8 * i)).toNat + 8 ≤ 2^64
  rw [eq]
  omega

theorem MemoryPre.outputOutsideLoopStack (h : MemoryPre code fr) {i : Nat} (hi : i < 4) :
    Outside [loopStack fr] (wordAddr fr.rdx 64 i) 8 := by
  have bounds := h.outputIn hi
  refine ⟨bounds.2.2, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  have sep := h.outputStack.2 _ (List.mem_cons_self ..)
  have room := h.stackRoom
  have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := h.stackNat (by decide : 80 ≤ 208)
  change fr.rdx.toNat + 32 ≤ fr.low.toNat ∨
    fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdx.toNat at sep
  simp only [loopStack, buffer, sp80]
  simp only [InRegion, buffer] at bounds
  omega

end K256.Proofs.ParseSignature.Fill
