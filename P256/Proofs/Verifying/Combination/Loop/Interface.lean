import P256.Proofs.Verifying.Combination.Prologue
import P256.Proofs.Verifying.Combination.Table.Interface
import P256.Proofs.Verifying.Combination.Naf.Output

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame

namespace Loop

def tablesRegion (address : BitVec 64) : MemoryRegion := ⟨address.toNat, 1536⟩

def digitsRegion (address : BitVec 64) : MemoryRegion := ⟨address.toNat, 544⟩

structure MultiPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (tables digits : BitVec 64) : Prop extends CalleePre s boundary 0x10efd0 48 96 1432 where
  tablePointer : memLoad s.external (s.regValue .rsi) 64 = tables
  tableEnd : memLoad s.external (s.regValue .rsi + 8) 64 = tables + 1536
  digitPointer : memLoad s.external (s.regValue .rsi + 16) 64 = digits
  digitEnd : memLoad s.external (s.regValue .rsi + 24) 64 = digits + 544
  startIndex : memLoad s.external (s.regValue .rsi + 32) 64 = 0
  endIndex : memLoad s.external (s.regValue .rsi + 40) 64 = 2
  tablesBounded : (tablesRegion tables).Bounded
  tablesAllocated : (tablesRegion tables).Allocated s.external
  tablesOutput : (tablesRegion tables).Disjoint (registerRegion s .rdi 96)
  tablesStack : (tablesRegion tables).Disjoint (Stack.region s 1432)
  digitsBounded : (digitsRegion digits).Bounded
  digitsAllocated : (digitsRegion digits).Allocated s.external
  digitsOutput : (digitsRegion digits).Disjoint (registerRegion s .rdi 96)
  digitsStack : (digitsRegion digits).Disjoint (Stack.region s 1432)

def MultiCorrect : Prop :=
  ∀ [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (tables digits : BitVec 64) (p q : Projective) (u v : Nat),
    MultiPre s boundary tables digits →
    Table.TableAt s tables (Table.oddTable p) →
    Table.TableAt s (tables + 768) (Table.oddTable q) →
    Naf.NafAt s digits u → Naf.NafAt s (digits + 272) v →
    u < 2^256 → v < 2^256 → p.valid → q.valid →
      ∃ t result, CalleeResult s t boundary 96 1432 ∧
        ProjectiveAt t (s.regValue .rdi) result ∧ RepresentsSum result p q u v

end Loop
end P256.Proofs.Verifying.Combination
