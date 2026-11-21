import K256.Proofs.Common.SignatureRun
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Generate.Memory
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Generate.Generator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def callFrame (target : Label) (rip : BitVec 64) : StackFrame Value Label signature Reg.count :=
  { target, kept := #v[], arity := rfl, guard := some ⟨64, rip⟩ }

def entryArgs (s : RamState) : Vector Value Reg.count :=
  let sp := s.regValue .rsp
  let a : Vector Value 53 := (lifted.locationOf .l102510 s).arguments
  (((((a.set 3 ⟨64, s.regValue .rdi⟩).set 4 ⟨64, sp - 288⟩).set 6 ⟨64, sp - 208⟩).set 7
    ⟨64, sp - 192⟩).set 14 ⟨64, sp - 192⟩)

def entryMemory (s : RamState) : Ram :=
  let sp := s.regValue .rsp
  let m1 := memStore s.external (sp - 8) (s.regValue .r14)
  let m2 := memStore m1 (sp - 16) (s.regValue .rbx)
  let m3 := memStore m2 (sp - 208) (s.regValue .rsi)
  let m4 := memStore m3 (sp - 200) (s.regValue .rdx)
  memStore m4 (sp - 288) (0x102539 : BitVec 64)

private theorem entryBlock {code : CodeMap} {mem : Ram} {a : Vector Value 53}
    {sp dx bx si di old14 : BitVec 64} (hsp : a[4].get 64 = sp) (hdx : a[2].get 64 = dx)
    (hbx : a[3].get 64 = bx) (hsi : a[6].get 64 = si) (hdi : a[7].get 64 = di)
    (h14 : a[14].get 64 = old14) :
    let m1 := memStore mem (sp - 8) old14
    let m2 := memStore m1 (sp - 16) bx
    let m3 := memStore m2 (sp - 208) si
    let m4 := memStore m3 (sp - 200) dx
    StoreOk code mem (sp - 8) 8 0x102510 2 →
    StoreOk code m1 (sp - 16) 8 0x102512 1 →
    StoreOk code m2 (sp - 208) 8 0x10251d 5 →
    StoreOk code m3 (sp - 200) 8 0x102522 5 →
    StoreOk code m4 (sp - 288) 8 0x102534 5 →
    program.runBlock (dialect code) ⟨.l102510, a, mem⟩ =
      .call ⟨.l105f30, ((((a.set 3 ⟨64, di⟩).set 4 ⟨64, sp - 288⟩).set 6 ⟨64, sp - 208⟩).set 7
        ⟨64, sp - 192⟩).set 14 ⟨64, sp - 192⟩, memStore m4 (sp - 288) (0x102539 : BitVec 64)⟩
        (callFrame .l102539 0x102539) := by
  dsimp only
  intro g1 g2 g3 g4 g5
  cfg_eval
  simp only [hsp, hdx, hbx, hsi, hdi, h14, g1, g2, g3, g4, g5, ↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun he => Vector.ext fun i hi => he ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [Vector.getElem_set] <;> rfl

theorem entry {s : RamState} {random : ByteArray} (call : ValidCall signingKeyGenerateFromRng s [random]) :
    program.runBlock (dialect Extracted.programImage) (lifted.locationOf .l102510 s) =
      .call ⟨.l105f30, entryArgs s, entryMemory s⟩ (callFrame .l102539 0x102539) := by
  let sp := s.regValue .rsp
  let a : Vector Value 53 := (lifted.locationOf .l102510 s).arguments
  let m1 := memStore s.external (sp - 8) (s.regValue .r14)
  let m2 := memStore m1 (sp - 16) (s.regValue .rbx)
  let m3 := memStore m2 (sp - 208) (s.regValue .rsi)
  let m4 := memStore m3 (sp - 200) (s.regValue .rdx)
  have inc := fun x hx => Common.fnCode_subset_programImage x (code_l102510 x hx)
  have g1 : StoreOk Extracted.programImage s.external (sp - 8) 8 0x102510 2 := by
    apply ParseSignature.storeOk_of_codeRange (off := 0) _ inc (by decide)
    exact stackWritable (off := 8) call (by decide) (by decide) (by decide)
  have g2 : StoreOk Extracted.programImage m1 (sp - 16) 8 0x102512 1 := by
    apply ParseSignature.storeOk_of_codeRange (off := 2) _ inc (by decide)
    apply Writable.memStore
    exact stackWritable (off := 16) call (by decide) (by decide) (by decide)
  have g3 : StoreOk Extracted.programImage m2 (sp - 208) 8 0x10251d 5 := by
    apply ParseSignature.storeOk_of_codeRange (off := 13) _ inc (by decide)
    apply Writable.memStore
    apply Writable.memStore
    exact stackWritable (off := 208) call (by decide) (by decide) (by decide)
  have g4 : StoreOk Extracted.programImage m3 (sp - 200) 8 0x102522 5 := by
    apply ParseSignature.storeOk_of_codeRange (off := 18) _ inc (by decide)
    apply Writable.memStore
    apply Writable.memStore
    apply Writable.memStore
    exact stackWritable (off := 200) call (by decide) (by decide) (by decide)
  have g5 : StoreOk Extracted.programImage m4 (sp - 288) 8 0x102534 5 := by
    apply ParseSignature.storeOk_of_codeRange (off := 36) _ inc (by decide)
    apply Writable.memStore
    apply Writable.memStore
    apply Writable.memStore
    apply Writable.memStore
    exact stackWritable (off := 288) call (by decide) (by decide) (by decide)
  apply entryBlock (a := a) (sp := sp) (dx := s.regValue .rdx) (bx := s.regValue .rbx)
    (si := s.regValue .rsi) (di := s.regValue .rdi) (old14 := s.regValue .r14)
    _ _ _ _ _ _ g1 g2 g3 g4 g5
  all_goals simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl

theorem entryMemory_frame {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) :
    RamWriteFrame s.external (entryMemory s) [Stack.region s signingKeyGenerateFromRng.minStackBytes] := by
  unfold entryMemory
  apply RamWriteFrame.memStore _ _ ⟨_, List.mem_cons_self, stackRange (off := 288) call (by decide) (by decide)⟩
  apply RamWriteFrame.memStore _ _ ⟨_, List.mem_cons_self, stackRange (off := 200) call (by decide) (by decide)⟩
  apply RamWriteFrame.memStore _ _ ⟨_, List.mem_cons_self, stackRange (off := 208) call (by decide) (by decide)⟩
  apply RamWriteFrame.memStore _ _ ⟨_, List.mem_cons_self, stackRange (off := 16) call (by decide) (by decide)⟩
  apply RamWriteFrame.memStore _ _ ⟨_, List.mem_cons_self, stackRange (off := 8) call (by decide) (by decide)⟩
  exact RamWriteFrame.refl _ _

theorem entryMemory_load (s : RamState) :
    let sp := s.regValue .rsp
    let mem := entryMemory s
    memLoad mem (sp - 208) 64 = s.regValue .rsi ∧
    memLoad mem (sp - 200) 64 = s.regValue .rdx ∧
    memLoad mem (sp - 288) 64 = 0x102539 ∧
    memLoad mem (sp - 16) 64 = s.regValue .rbx ∧
    memLoad mem (sp - 8) 64 = s.regValue .r14 ∧
    memLoad mem sp 64 = (returnBoundary s).rip := by
  intro sp mem
  dsimp only [mem, entryMemory]
  repeat' constructor
  all_goals
    repeat' first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets
          (addr_sub sp _) (addr_sub sp _) (by decide))]
      | rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets
          (addr_sub sp _) (addr_self sp) (by decide))]
  rfl

end K256.Proofs.Generate.Generator
