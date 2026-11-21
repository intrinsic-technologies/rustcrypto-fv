import K256.Proofs.Verify.Hash.Compression.Values.Program
import K256.Proofs.Common.Refine.Lemma.Store
import X86Proofs.Program.ReadWrite.Bytes

namespace K256.Proofs.Verify.Hash.Compression
open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift
namespace Values

def ValidSpill (offset bytes : Nat) : Prop :=
  offset % 4 = 0 ∧ (offset + bytes ≤ 192 ∨ 208 ≤ offset ∧ offset + bytes ≤ 288)

def Op.validSpills : Op → Prop
  | .store32 off _ | .addStack32 off _ => ValidSpill off 4
  | .store64 off _ => ValidSpill off 8
  | _ => True

def Op.spill (op : Op) (ctx : ValueContext) (s : Compression.Values) (m : Ram) : Ram :=
  match op with
  | .store32 off src => memStore m (ctx.stackPointer + BitVec.ofNat 64 off) ((s.regs src).setWidth 32)
  | .store64 off src => memStore m (ctx.stackPointer + BitVec.ofNat 64 off) (s.regs src)
  | .addStack32 off src => memStore m (ctx.stackPointer + BitVec.ofNat 64 off)
      (s.stack off + (s.regs src).setWidth 32)
  | _ => m

def spillRun (ctx : ValueContext) : List Op → Compression.Values → Ram → Ram
  | [], _, m => m
  | op :: ops, s, m => spillRun ctx ops (op.eval ctx s) (op.spill ctx s m)

def StackMatches (sp : BitVec 64) (s : Compression.Values) (m : Ram) : Prop :=
  ∀ off, off % 4 = 0 → off + 4 ≤ 336 → memLoad m (sp + BitVec.ofNat 64 off) 32 = s.stack off

private theorem StackMatches.write32 {sp : BitVec 64} {s : Compression.Values} {m : Ram}
    (agree : StackMatches sp s m) (off : Nat) (value : BitVec 32)
    (align : off % 4 = 0) (bound : off + 4 ≤ 336) :
    StackMatches sp (s.write32 off value) (memStore m (sp + BitVec.ofNat 64 off) value) := by
  intro readOff readAlign readBound
  change _ = (if readOff = off then value else s.stack readOff)
  by_cases same : readOff = off
  · subst readOff
    rw [ite_eq_left rfl]
    exact memLoad_memStore_same m _ value (by decide) (by decide)
  · simp only [ite_eq_right same]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.offsets sp (by omega) (by omega) (by omega))]
    exact agree readOff readAlign readBound

private theorem StackMatches.write64 {sp : BitVec 64} {s : Compression.Values} {m : Ram}
    (agree : StackMatches sp s m) (off : Nat) (value : BitVec 64)
    (align : off % 4 = 0) (bound : off + 8 ≤ 336) :
    StackMatches sp (s.write64 off value) (memStore m (sp + BitVec.ofNat 64 off) value) := by
  intro readOff readAlign readBound
  change _ = (if readOff = off + 4 then value.extractLsb' 32 32
    else if readOff = off then value.setWidth 32 else s.stack readOff)
  by_cases hi : readOff = off + 4
  · subst readOff
    rw [ite_eq_left rfl]
    have addr : sp + BitVec.ofNat 64 (off + 4) =
        sp + BitVec.ofNat 64 off + BitVec.ofNat 64 4 := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    exact K256.Proofs.Refine.memLoad_memStore_within m value 32 4
      addr (by decide) (by decide) (by decide)
  · by_cases lo : readOff = off
    · subst readOff
      simp only [ite_eq_right hi, BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
      exact K256.Proofs.Refine.memLoad_memStore_within m value 32 0
        (BitVec.add_zero _).symm (by decide) (by decide) (by decide)
    · simp only [ite_eq_right hi, ite_eq_right lo]
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _
        (RangeApart.offsets sp (by omega) (by omega) (by omega))]
      exact agree readOff readAlign readBound

theorem spillRun_matches (ctx : ValueContext) (ops : List Op) (s : Compression.Values) (m : Ram)
    (valid : ∀ op ∈ ops, op.validSpills) (agree : StackMatches ctx.stackPointer s m) :
    StackMatches ctx.stackPointer (run ctx ops s) (spillRun ctx ops s m) := by
  induction ops generalizing s m with
  | nil => exact agree
  | cons op ops ih =>
      have head := valid op List.mem_cons_self
      have tail (step : Op) (mem : step ∈ ops) := valid step (List.mem_cons_of_mem _ mem)
      apply ih _ _ tail
      cases op <;> try exact agree
      case store32 off src =>
        exact agree.write32 off _ head.1 (by rcases head.2 with h | h <;> omega)
      case store64 off src =>
        exact agree.write64 off _ head.1 (by rcases head.2 with h | h <;> omega)
      case addStack32 off src =>
        exact agree.write32 off _ head.1 (by rcases head.2 with h | h <;> omega)

theorem StackMatches.load64 {sp : BitVec 64} {s : Compression.Values} {m : Ram}
    (h : StackMatches sp s m) (off : Nat) (align : off % 4 = 0) (bound : off + 8 ≤ 336) :
    memLoad m (sp + BitVec.ofNat 64 off) 64 = s.stack (off + 4) ++ s.stack off := by
  let addr := sp + BitVec.ofNat 64 off
  have hi : (memLoad m addr 64).extractLsb' 32 32 = s.stack (off + 4) := by
    rw [K256.Proofs.Refine.extractLsb'_memLoad m addr 32 32 (by decide) (by decide) (by decide)]
    simpa only [addr, BitVec.add_assoc, ← BitVec.ofNat_add] using h (off + 4) (by omega) bound
  have lo : (memLoad m addr 64).extractLsb' 0 32 = s.stack off := by
    rw [K256.Proofs.Refine.extractLsb'_memLoad m addr 0 32 (by decide) (by decide) (by decide)]
    change memLoad m (addr + 0) 32 = _
    exact (congrArg (fun a => memLoad m a 32) (BitVec.add_zero addr)).trans (h off align (by omega))
  rw [← hi, ← lo, BitVec.extractLsb'_append_extractLsb']

end Values
end K256.Proofs.Verify.Hash.Compression
