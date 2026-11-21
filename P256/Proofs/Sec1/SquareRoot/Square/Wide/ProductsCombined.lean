import P256.Proofs.Sec1.SquareRoot.Square.Wide.BodyInterface
import P256.Proofs.Sec1.SquareRoot.Square.Wide.BlockCompose
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Products
import P256.Proofs.Sec1.SquareRoot.Square.Wide.CrossSums
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Diagonals
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Accumulate
import P256.Proofs.Sec1.SquareRoot.Square.Wide.StoresLow
import P256.Proofs.Sec1.SquareRoot.Square.Wide.StoresHigh

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def productsEffect (s : RamState) : Effect :=
  let v111b66 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111b66 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111b74 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let hv111b74 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let v111b86 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111b86 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111b92 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let hv111b92 := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let v111b9e := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) * ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let hv111b9e := mulHigh64 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  { rip := 0x11cc07
    writes := [
      ⟨(.reg 0 : Operand 64), v111b9e⟩,
      ⟨(.reg 1 : Operand 64), v111b86⟩,
      ⟨(.reg 2 : Operand 64), hv111b9e⟩,
      ⟨(.reg 3 : Operand 64), v111b92⟩,
      ⟨(.reg 5 : Operand 64), hv111b9e⟩,
      ⟨(.reg 6 : Operand 64), hv111b86⟩,
      ⟨(.reg 8 : Operand 64), v111b9e⟩,
      ⟨(.reg 9 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)⟩,
      ⟨(.reg 10 : Operand 64), hv111b66⟩,
      ⟨(.reg 11 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)⟩,
      ⟨(.reg 12 : Operand 64), hv111b92⟩,
      ⟨(.reg 13 : Operand 64), v111b74⟩,
      ⟨(.reg 14 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)⟩,
      ⟨(.reg 15 : Operand 64), ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64), hv111b74⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64), v111b66⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem products_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BodyPre (codeRange 0x11cbb8 bodyBytes)
      (Effect.post productsEffect) := by
  intro s ready loaded hp
  have pl : LowerProductsPre s := by
    refine ⟨hp.rip, ?_, ?_, ?_⟩
    · intro i hi
      exact hp.input i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl <;> simp)
    · intro i hi
      exact hp.stackWrite i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> simp)
    · intro i hi o n hn
      exact hp.stackCode i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> simp) o n hn
  obtain ⟨n1, t, run1, ready1, _, h1⟩ := lowerProducts_correct boundary hout s ready
    (loaded.mono (codeRange_slice_subset 0x11cbb8 bodyBytes 0 39)) pl
  have av1 : (lowerProductsEffect s).Avoids (codeRange 0x11cbb8 bodyBytes) := by
    apply Effect.avoids_codeRange
    x86_norm [lowerProductsEffect]
    exact ⟨hp.stackCode 32 (by simp) 0x1cbb8 297 (by decide), hp.stackCode 8 (by simp) 0x1cbb8 297 (by decide)⟩
  have loaded1 := h1.codeIn av1 loaded
  have rsi : (Operand.reg 6 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s :=
    h1.agrees.read (by simp [lowerProductsEffect, Effect.components])
  have pu : UpperProductsPre t := by
    refine ⟨h1.rip, ?_⟩
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    rw [rsi]
    exact (hp.input 24 (by simp)).of_holds h1
  obtain ⟨n2, u, run2, ready2, _, h2⟩ := upperProducts_correct boundary hout t ready1
    (loaded1.mono (codeRange_slice_subset 0x11cbb8 bodyBytes 39 40)) pu
  have ext : u.external = t.external := h2.agrees.external
    (by simp [upperProductsEffect, Effect.components, Component.Covers])
  have loaded2 : CodeIn (codeRange 0x11cbb8 bodyBytes) u := loaded1.of_external_eq ext
  have h24 : (Operand.mem ((Operand.reg 6 : Operand 64).read t+24) : Operand 64).read t =
      (Operand.mem ((Operand.reg 6 : Operand 64).read s+24) : Operand 64).read s := by
    rw [rsi]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    apply h1.agrees.memory
    intro c hc hcov
    simp only [lowerProductsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    all_goals obtain ⟨j, hj, he⟩ := hcov
    · exact hp.stackInput 32 (by simp) 24 (by simp) j hj i hi he.symm
    · exact hp.stackInput 8 (by simp) 24 (by simp) j hj i hi he.symm
  rcases h1.writes with ⟨r9, r11, r14, r10, _, _, r13, m32, m8⟩
  have ws2 := h2.writes
  simp only [upperProductsEffect, Write.AllHold, r9, r11, r14, h24] at ws2
  rcases ws2 with ⟨r15, r6, r1, r12, r3, r8, r5, r0, r2⟩
  have keep (r : BitVec 5) (hr : r ∈ ([9, 10, 11, 13, 14] : List (BitVec 5))) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read t := by
    apply h2.agrees.read
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals simp [upperProductsEffect, Effect.components]
  refine ⟨n1+n2, u, run1.trans run2, ready2, loaded2, ?_⟩
  refine ⟨h2.rip, ?_, ?_, ?_⟩
  · simp only [productsEffect, Write.AllHold]
    refine ⟨r0, r1, r2, r3, r5, r6, r8, (keep 9 (by simp)).trans r9,
      (keep 10 (by simp)).trans r10, (keep 11 (by simp)).trans r11, r12,
      (keep 13 (by simp)).trans r13, (keep 14 (by simp)).trans r14, r15, ?_, ?_⟩
    · change memLoad u.external _ 64 = _
      rw [ext]
      exact m8
    · change memLoad u.external _ 64 = _
      rw [ext]
      exact m32
  · simp [productsEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply (h1.agrees.trans h2.agrees).mono
    simp [lowerProductsEffect, upperProductsEffect, productsEffect, Effect.components]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
