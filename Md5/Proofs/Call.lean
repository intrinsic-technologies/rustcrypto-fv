import Md5.Spec.Program

namespace Md5.Proofs.Call

open Md5.Spec.Program Prelude X86

theorem separation_pair {input output stack : MemoryRegion}
    (h : Md5.Spec.Program.MemorySeparation #v[output, stack] [input]) :
    MemoryRegion.PairwiseDisjoint #v[input, output, stack] ∧
      ∀ region ∈ #v[output, stack],
        region.Avoids fun address => InProgram address ∨ InPageTables address := by
  refine ⟨?_, fun region hr ↦ (h.2 region hr).2⟩
  have ho := (h.2 output (by simp)).1 input (by simp)
  have hs := (h.2 stack (by simp)).1 input (by simp)
  have hw := h.1 0 1 (by decide)
  intro i j hij
  have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ho
  · exact hs
  · exact hw

namespace Compress

open Md5.Spec.Program.Compress

def ValidInput (s : Machine.RamState) (input : ByteArray) : Prop :=
  let region := inputRegion s input
  region.Bounded ∧
  region.HasLength (64 * (s.regValue .rdx).toNat) ∧
  region.HasBytes s.external input

def ValidBuffer (s : Machine.RamState) (buffer : Standards.RFC.MD5.Buffer) : Prop :=
  let region := outputRegion s
  region.Bounded ∧
  region.HasBytes s.external ⟨buffer.toBytes.toArray⟩

def MemorySeparation (s : Machine.RamState) (input : ByteArray) : Prop :=
  let stack := Stack.region s minStackBytes
  MemoryRegion.PairwiseDisjoint #v[inputRegion s input, outputRegion s, stack] ∧
  ∀ region ∈ #v[outputRegion s, stack],
    region.Avoids fun address => InProgram address ∨ InPageTables address

end Compress

namespace Digest

open Md5.Spec.Program.Digest

def ValidInput (s : Machine.RamState) (input : ByteArray) : Prop :=
  let region := inputRegion s input
  region.Bounded ∧
  region.HasLength (s.regValue .rsi).toNat ∧
  region.HasBytes s.external input

def ValidOutput (s : Machine.RamState) : Prop :=
  let region := outputRegion s
  region.Bounded ∧
  region.Allocated s.external

def MemorySeparation (s : Machine.RamState) (input : ByteArray) : Prop :=
  let stack := Stack.region s minStackBytes
  MemoryRegion.PairwiseDisjoint #v[inputRegion s input, outputRegion s, stack] ∧
  ∀ region ∈ #v[outputRegion s, stack],
    region.Avoids fun address => InProgram address ∨ InPageTables address

end Digest

end Md5.Proofs.Call
