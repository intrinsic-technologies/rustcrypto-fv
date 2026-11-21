import K256.Proofs.Common.CallMemory
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Common.Refine.Lemma.Region
import K256.Proofs.Common.Tactic
import K256.Proofs.Ecdh.Wrapper.Frame
import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR

def parserArgs (a : Vector Value 53) (sp dst peer word0 word8 : BitVec 64) :
    Vector Value 53 :=
  let a := (a.set 0 ⟨64, word0⟩).set 1 ⟨64, word8⟩
  let a := (a.set 3 ⟨64, dst⟩).set 4 ⟨64, sp - 6160⟩
  let a := (a.set 6 ⟨64, sp - 6064⟩).set 7 ⟨64, sp - 5808⟩
  (a.set 14 ⟨64, peer⟩).set 15 ⟨64, sp - 5808⟩

def entryArgs (s : RamState) : Vector Value Reg.count :=
  parserArgs (lifted.locationOf .l101660 s).arguments (stackPtr s) (s.regValue .rdi)
    (s.regValue .rdx) (memLoad s.external (s.regValue .rsi) 64)
    (memLoad s.external (s.regValue .rsi + 8) 64)

def entryMemory (s : RamState) : Ram :=
  let m1 := memStore s.external (stackPtr s - 8) (s.regValue .rbp)
  let m2 := memStore m1 (stackPtr s - 16) (s.regValue .r15)
  let m3 := memStore m2 (stackPtr s - 24) (s.regValue .r14)
  let m4 := memStore m3 (stackPtr s - 32) (s.regValue .r13)
  let m5 := memStore m4 (stackPtr s - 40) (s.regValue .r12)
  let m6 := memStore m5 (stackPtr s - 48) (s.regValue .rbx)
  let m7 := memStore m6 (stackPtr s - 4144) (0 : BitVec 64)
  let m8 := memStore m7 (stackPtr s - 6040) (memLoad s.external (s.regValue .rsi + 24) 64)
  let m9 := memStore m8 (stackPtr s - 6048) (memLoad s.external (s.regValue .rsi + 16) 64)
  let m10 := memStore m9 (stackPtr s - 6056) (memLoad s.external (s.regValue .rsi + 8) 64)
  let m11 := memStore m10 (stackPtr s - 6064) (memLoad s.external (s.regValue .rsi) 64)
  let m12 := memStore m11 (stackPtr s - 6160) (0x1016be : BitVec 64)
  m12

private theorem inputLoad {s : RamState} {secret key : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) {m : Ram}
    (frame : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    (off : Nat) (fits : off + 8 ≤ 32) :
    let addr := s.regValue .rsi + BitVec.ofNat 64 off
    LoadOk m addr 8 ∧ memLoad m addr 64 = memLoad s.external addr 64 := by
  let r := registerRegion s .rsi 32
  let stack := Stack.region s ecdhDiffieHellman.minStackBytes
  have hr : ValidInput s r secret := call.inputsInMemory.1
  have low : (s.regValue .rsi).toNat + 32 < 2^32 := hr.2.1
  have size : secret.size = 32 := hr.2.2.1
  have ha : (s.regValue .rsi + BitVec.ofNat 64 off).toNat = (s.regValue .rsi).toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have read := Readable.of_hasBytes hr.2.2 hr.2.1
  change Readable s.external (BitVec.ofNat 64 (s.regValue .rsi).toNat) secret.size at read
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, size] at read
  have sep : MemorySeparation [outputRegion ecdhDiffieHellman s, stack]
      [r, registerRegion s .rdx 33] := call.separation
  have disj := (sep.2 stack (by simp)).2 r List.mem_cons_self
  have apart := apart_of_disjoint disj (by
    change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10088)
    omega) (by change 0 < 32; decide)
  change stack.start + stack.size ≤ (s.regValue .rsi).toNat ∨
    (s.regValue .rsi).toNat + 32 ≤ stack.start at apart
  exact ⟨LoadOk.of_region (read.of_frame frame) (by rw [ha]; omega) (by rw [ha]; omega),
    frame.memLoad_eq ⟨by rw [ha]; omega, fun x hx => by
      obtain rfl := List.mem_singleton.mp hx
      change (s.regValue .rsi + BitVec.ofNat 64 off).toNat + 8 ≤ stack.start ∨
        stack.start + stack.size ≤ (s.regValue .rsi + BitVec.ofNat 64 off).toNat
      rw [ha]
      omega⟩⟩

private theorem storeFrame {s : RamState} {secret key : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) {m : Ram}
    (frame : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes])
    {d : Nat} (depth : d ≤ 10088) (v : BitVec 64) :
    RamWriteFrame s.external (memStore m (stackPtr s - BitVec.ofNat 64 d) v)
      [Stack.region s ecdhDiffieHellman.minStackBytes] :=
  frame.memStore v ⟨_, List.mem_cons_self, Common.stackRange call.stackAvailable depth (by omega)⟩

theorem entryMemory_frame {s : RamState} {secret key : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) :
    RamWriteFrame s.external (entryMemory s) [Stack.region s ecdhDiffieHellman.minStackBytes] := by
  unfold entryMemory
  apply storeFrame (d := 6160) call _ (by decide)
  apply storeFrame (d := 6064) call _ (by decide)
  apply storeFrame (d := 6056) call _ (by decide)
  apply storeFrame (d := 6048) call _ (by decide)
  apply storeFrame (d := 6040) call _ (by decide)
  apply storeFrame (d := 4144) call _ (by decide)
  apply storeFrame (d := 48) call _ (by decide)
  apply storeFrame (d := 40) call _ (by decide)
  apply storeFrame (d := 32) call _ (by decide)
  apply storeFrame (d := 24) call _ (by decide)
  apply storeFrame (d := 16) call _ (by decide)
  apply storeFrame (d := 8) call _ (by decide)
  exact RamWriteFrame.refl _ _

set_option maxHeartbeats 900000 in
theorem entryMemory_load (s : RamState) :
    memLoad (entryMemory s) (stackPtr s - 8) 64 = (s.regValue .rbp) ∧
    memLoad (entryMemory s) (stackPtr s - 16) 64 = (s.regValue .r15) ∧
    memLoad (entryMemory s) (stackPtr s - 24) 64 = (s.regValue .r14) ∧
    memLoad (entryMemory s) (stackPtr s - 32) 64 = (s.regValue .r13) ∧
    memLoad (entryMemory s) (stackPtr s - 40) 64 = (s.regValue .r12) ∧
    memLoad (entryMemory s) (stackPtr s - 48) 64 = (s.regValue .rbx) ∧
    memLoad (entryMemory s) (stackPtr s - 4144) 64 = (0 : BitVec 64) ∧
    memLoad (entryMemory s) (stackPtr s - 6040) 64 = (memLoad s.external (s.regValue .rsi + 24) 64) ∧
    memLoad (entryMemory s) (stackPtr s - 6048) 64 = (memLoad s.external (s.regValue .rsi + 16) 64) ∧
    memLoad (entryMemory s) (stackPtr s - 6056) 64 = (memLoad s.external (s.regValue .rsi + 8) 64) ∧
    memLoad (entryMemory s) (stackPtr s - 6064) 64 = (memLoad s.external (s.regValue .rsi) 64) ∧
    memLoad (entryMemory s) (stackPtr s - 6160) 64 = (0x1016be : BitVec 64) := by
  unfold entryMemory
  repeat' apply And.intro
  all_goals simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart]

theorem entryMemory_saved (s : RamState) : Wrapper.Saved s (entryMemory s) := by
  obtain ⟨rbp, r15, r14, r13, r12, rbx, _⟩ := entryMemory_load s
  constructor
  · intro slot hs
    simp only [Wrapper.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rbp
    · exact r15
    · exact r14
    · exact r13
    · exact r12
    · exact rbx
  · change memLoad (entryMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    unfold entryMemory
    repeat' rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets
      (addr_sub (stackPtr s) _) (addr_self (stackPtr s)) (by decide))]

set_option maxHeartbeats 800000 in
private theorem entryBlock (a : Vector Value 53) {code : CodeMap}
    {sp dst peer src bp bx r12 r13 r14 r15 w0 w8 w16 w24 : BitVec 64}
    {m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 : Ram}
    (h2 : a[2].get 64 = peer)
    (h3 : a[3].get 64 = bx)
    (h4 : a[4].get 64 = sp)
    (h5 : a[5].get 64 = bp)
    (h6 : a[6].get 64 = src)
    (h7 : a[7].get 64 = dst)
    (h12 : a[12].get 64 = r12)
    (h13 : a[13].get 64 = r13)
    (h14 : a[14].get 64 = r14)
    (h15 : a[15].get 64 = r15)
    (g1 : StoreOk code m0 (sp - 8) 8 0x101660 1)
    (step1 : memStore m0 (sp - 8) bp = m1)
    (g2 : StoreOk code m1 (sp - 16) 8 0x101661 2)
    (step2 : memStore m1 (sp - 16) r15 = m2)
    (g3 : StoreOk code m2 (sp - 24) 8 0x101663 2)
    (step3 : memStore m2 (sp - 24) r14 = m3)
    (g4 : StoreOk code m3 (sp - 32) 8 0x101665 2)
    (step4 : memStore m3 (sp - 32) r13 = m4)
    (g5 : StoreOk code m4 (sp - 40) 8 0x101667 2)
    (step5 : memStore m4 (sp - 40) r12 = m5)
    (g6 : StoreOk code m5 (sp - 48) 8 0x101669 1)
    (step6 : memStore m5 (sp - 48) bx = m6)
    (g7 : StoreOk code m6 (sp - 4144) 8 0x101671 8)
    (step7 : memStore m6 (sp - 4144) (0 : BitVec 64) = m7)
    (g8 : StoreOk code m7 (sp - 6040) 8 0x10168a 5)
    (step8 : memStore m7 (sp - 6040) w24 = m8)
    (g9 : StoreOk code m8 (sp - 6048) 8 0x101693 5)
    (step9 : memStore m8 (sp - 6048) w16 = m9)
    (g10 : StoreOk code m9 (sp - 6056) 8 0x10169f 5)
    (step10 : memStore m9 (sp - 6056) w8 = m10)
    (g11 : StoreOk code m10 (sp - 6064) 8 0x1016a4 5)
    (step11 : memStore m10 (sp - 6064) w0 = m11)
    (g12 : StoreOk code m11 (sp - 6160) 8 0x1016b9 5)
    (step12 : memStore m11 (sp - 6160) (0x1016be : BitVec 64) = m12)
    (load24 : LoadOk m7 (src + 24) 8) (word24 : memLoad m7 (src + 24) 64 = w24)
    (load16 : LoadOk m8 (src + 16) 8) (word16 : memLoad m8 (src + 16) 64 = w16)
    (load0 : LoadOk m9 src 8) (word0 : memLoad m9 src 64 = w0)
    (load8 : LoadOk m9 (src + 8) 8) (word8 : memLoad m9 (src + 8) 64 = w8) :
    program.runBlock (dialect code) ⟨.l101660, a, m0⟩ =
      .call ⟨.l109e60, parserArgs a sp dst peer w0 w8, m12⟩
        ⟨.l1016be, #v[], rfl, some ⟨64, 0x1016be⟩⟩ := by
  cfg_eval [h2, h3, h4, h5, h6, h7, h12, h13, h14, h15,
    step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12,
    word0, word8, word16, word24]
  simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12,
    load0, load8, load16, load24, ↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun he => Vector.ext fun i hi => he ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [parserArgs, Vector.getElem_set] <;> rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem entry {s : RamState} {secret key : ByteArray} (call : ValidCall ecdhDiffieHellman s [secret, key]) :
    program.runBlock (dialect Extracted.programImage) (lifted.locationOf .l101660 s) =
      .call ⟨.l109e60, entryArgs s, entryMemory s⟩
        ⟨.l1016be, #v[], rfl, some ⟨64, 0x1016be⟩⟩ := by
  let a : Vector Value 53 := (lifted.locationOf .l101660 s).arguments
  change program.runBlock _ ⟨.l101660, a, s.external⟩ = _
  have h2 : a[2].get 64 = s.regValue .rdx := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h3 : a[3].get 64 = s.regValue .rbx := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h4 : a[4].get 64 = stackPtr s := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h5 : a[5].get 64 = s.regValue .rbp := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h6 : a[6].get 64 = s.regValue .rsi := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h7 : a[7].get 64 = s.regValue .rdi := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h12 : a[12].get 64 = s.regValue .r12 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h13 : a[13].get 64 = s.regValue .r13 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h14 : a[14].get 64 = s.regValue .r14 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h15 : a[15].get 64 = s.regValue .r15 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  let m1 := memStore s.external (stackPtr s - 8) (s.regValue .rbp)
  let m2 := memStore m1 (stackPtr s - 16) (s.regValue .r15)
  let m3 := memStore m2 (stackPtr s - 24) (s.regValue .r14)
  let m4 := memStore m3 (stackPtr s - 32) (s.regValue .r13)
  let m5 := memStore m4 (stackPtr s - 40) (s.regValue .r12)
  let m6 := memStore m5 (stackPtr s - 48) (s.regValue .rbx)
  let m7 := memStore m6 (stackPtr s - 4144) (0 : BitVec 64)
  let m8 := memStore m7 (stackPtr s - 6040) (memLoad s.external (s.regValue .rsi + 24) 64)
  let m9 := memStore m8 (stackPtr s - 6048) (memLoad s.external (s.regValue .rsi + 16) 64)
  let m10 := memStore m9 (stackPtr s - 6056) (memLoad s.external (s.regValue .rsi + 8) 64)
  let m11 := memStore m10 (stackPtr s - 6064) (memLoad s.external (s.regValue .rsi) 64)

  let regions := [Stack.region s ecdhDiffieHellman.minStackBytes]
  have f0 := RamWriteFrame.refl s.external regions
  have guard {m : Ram} (frame : RamWriteFrame s.external m regions) (d pos len : Nat)
      (depth : d ≤ 10088) (fits : pos + len ≤ bytes_l101660.length) :
      StoreOk Extracted.programImage m (stackPtr s - BitVec.ofNat 64 d) 8
        (0x101660 + BitVec.ofNat 64 pos) len :=
    ParseSignature.storeOk_of_codeRange
      ((Common.stackWritable call depth (by omega) (by decide)).of_frame frame)
      (fun x hx => Common.fnCode_subset_programImage x (code_l101660 x hx)) fits
  have g1 := guard f0 8 0 1 (by decide) (by decide)
  have f1 : RamWriteFrame s.external m1 regions := storeFrame (d := 8) call f0 (by decide) _
  have g2 := guard f1 16 1 2 (by decide) (by decide)
  have f2 : RamWriteFrame s.external m2 regions := storeFrame (d := 16) call f1 (by decide) _
  have g3 := guard f2 24 3 2 (by decide) (by decide)
  have f3 : RamWriteFrame s.external m3 regions := storeFrame (d := 24) call f2 (by decide) _
  have g4 := guard f3 32 5 2 (by decide) (by decide)
  have f4 : RamWriteFrame s.external m4 regions := storeFrame (d := 32) call f3 (by decide) _
  have g5 := guard f4 40 7 2 (by decide) (by decide)
  have f5 : RamWriteFrame s.external m5 regions := storeFrame (d := 40) call f4 (by decide) _
  have g6 := guard f5 48 9 1 (by decide) (by decide)
  have f6 : RamWriteFrame s.external m6 regions := storeFrame (d := 48) call f5 (by decide) _
  have g7 := guard f6 4144 17 8 (by decide) (by decide)
  have f7 : RamWriteFrame s.external m7 regions := storeFrame (d := 4144) call f6 (by decide) _
  have g8 := guard f7 6040 42 5 (by decide) (by decide)
  have f8 : RamWriteFrame s.external m8 regions := storeFrame (d := 6040) call f7 (by decide) _
  have g9 := guard f8 6048 51 5 (by decide) (by decide)
  have f9 : RamWriteFrame s.external m9 regions := storeFrame (d := 6048) call f8 (by decide) _
  have g10 := guard f9 6056 63 5 (by decide) (by decide)
  have f10 : RamWriteFrame s.external m10 regions := storeFrame (d := 6056) call f9 (by decide) _
  have g11 := guard f10 6064 68 5 (by decide) (by decide)
  have f11 : RamWriteFrame s.external m11 regions := storeFrame (d := 6064) call f10 (by decide) _
  have g12 := guard f11 6160 89 5 (by decide) (by decide)
  obtain ⟨l24, w24⟩ := inputLoad call f7 24 (by decide)
  obtain ⟨l16, w16⟩ := inputLoad call f8 16 (by decide)
  obtain ⟨l0, w0⟩ := inputLoad call f9 0 (by decide)
  obtain ⟨l8, w8⟩ := inputLoad call f9 8 (by decide)
  simp only [BitVec.add_zero] at l0 w0
  exact entryBlock a h2 h3 h4 h5 h6 h7 h12 h13 h14 h15
    g1 rfl g2 rfl g3 rfl g4 rfl g5 rfl g6 rfl g7 rfl g8 rfl g9 rfl g10 rfl g11 rfl g12 rfl
    l24 w24 l16 w16 l0 w0 l8 w8

end K256.Proofs.Ecdh.Scalar
