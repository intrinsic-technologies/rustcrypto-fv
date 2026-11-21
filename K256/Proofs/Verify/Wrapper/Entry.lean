import K256.Proofs.Verify.Wrapper.Frame
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.LIR

def parserArgs (a : Vector Value 53) (sp key msg len sig : BitVec 64) : Vector Value 53 :=
  let a := (a.set 2 ⟨64, 65⟩).set 3 ⟨64, len⟩
  let a := (a.set 4 ⟨64, sp - 544⟩).set 6 ⟨64, key⟩
  ((a.set 7 ⟨64, sp - 528⟩).set 14 ⟨64, msg⟩).set 15 ⟨64, sig⟩

def parserResume : StackFrame Value Label signature Reg.count :=
  ⟨.l102fe9, #v[], rfl, some ⟨64, 0x102fe9⟩⟩

set_option maxHeartbeats 800000 in
private theorem entryBlock (a : Vector Value 53) {code : CodeMap}
    {sp key msg len sig bx r12 r14 r15 : BitVec 64} {m0 m1 m2 m3 m4 m5 : Ram}
    (h1 : a[1].get 64 = sig)
    (h2 : a[2].get 64 = len)
    (h3 : a[3].get 64 = bx)
    (h4 : a[4].get 64 = sp)
    (h6 : a[6].get 64 = msg)
    (h7 : a[7].get 64 = key)
    (h12 : a[12].get 64 = r12)
    (h14 : a[14].get 64 = r14)
    (h15 : a[15].get 64 = r15)
    (g1 : StoreOk code m0 (sp - 8) 8 0x102fc0 2)
    (s1 : memStore m0 (sp - 8) r15 = m1)
    (g2 : StoreOk code m1 (sp - 16) 8 0x102fc2 2)
    (s2 : memStore m1 (sp - 16) r14 = m2)
    (g3 : StoreOk code m2 (sp - 24) 8 0x102fc4 2)
    (s3 : memStore m2 (sp - 24) r12 = m3)
    (g4 : StoreOk code m3 (sp - 32) 8 0x102fc6 1)
    (s4 : memStore m3 (sp - 32) bx = m4)
    (g5 : StoreOk code m4 (sp - 544) 8 0x102fe4 5)
    (s5 : memStore m4 (sp - 544) (0x102fe9 : BitVec 64) = m5) :
    program.runBlock (dialect code) ⟨.l102fc0, a, m0⟩ =
      .call ⟨.l106390, parserArgs a sp key msg len sig, m5⟩ parserResume := by
  cfg_eval [h1,h2,h3,h4,h6,h7,h12,h14,h15,s1,s2,s3,s4,s5]
  simp only [g1,g2,g3,g4,g5,↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [parserArgs, Vector.getElem_set] <;> rfl

set_option maxHeartbeats 1000000 in
theorem entry {s : RamState} {key message signature : ByteArray}
    (call : ValidCall verifyingKeyVerify s [key, message, signature]) :
    let a : Vector Value 53 := (lifted.locationOf .l102fc0 s).arguments
    program.runBlock (dialect Extracted.programImage) (lifted.locationOf .l102fc0 s) =
      .call ⟨.l106390, parserArgs a (stackPtr s) (s.regValue .rdi) (s.regValue .rsi)
        (s.regValue .rdx) (s.regValue .rcx), parserMemory s⟩ parserResume := by
  let a : Vector Value 53 := (lifted.locationOf .l102fc0 s).arguments
  have h1 : a[1].get 64 = s.regValue .rcx := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h2 : a[2].get 64 = s.regValue .rdx := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h3 : a[3].get 64 = s.regValue .rbx := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h4 : a[4].get 64 = s.regValue .rsp := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h6 : a[6].get 64 = s.regValue .rsi := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h7 : a[7].get 64 = s.regValue .rdi := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h12 : a[12].get 64 = s.regValue .r12 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h14 : a[14].get 64 = s.regValue .r14 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  have h15 : a[15].get 64 = s.regValue .r15 := by simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  let m0 := s.external
  have f0 := RamWriteFrame.refl s.external [stack s]
  have guard {m : Ram} (f : RamWriteFrame s.external m [stack s]) (d pos len : Nat)
      (depth : d ≤ 13000) (fits : pos + len ≤ bytes_l102fc0.length) :
      StoreOk Extracted.programImage m (stackPtr s - BitVec.ofNat 64 d) 8
        (0x102fc0 + BitVec.ofNat 64 pos) len :=
    ParseSignature.storeOk_of_codeRange
      ((Common.stackWritable call depth (by omega) (by decide)).of_frame f)
      (fun x hx => Common.fnCode_subset_programImage x (code_l102fc0 x hx)) fits
  have g1 := guard f0 8 0 2 (by decide) (by decide)
  let m1 := memStore m0 (stackPtr s - 8) (s.regValue .r15)
  have f1 : RamWriteFrame s.external m1 [stack s] := f0.memStore _
    ⟨_, List.mem_cons_self, Common.stackRange (off := 8) call.stackAvailable (by decide) (by decide)⟩
  have g2 := guard f1 16 2 2 (by decide) (by decide)
  let m2 := memStore m1 (stackPtr s - 16) (s.regValue .r14)
  have f2 : RamWriteFrame s.external m2 [stack s] := f1.memStore _
    ⟨_, List.mem_cons_self, Common.stackRange (off := 16) call.stackAvailable (by decide) (by decide)⟩
  have g3 := guard f2 24 4 2 (by decide) (by decide)
  let m3 := memStore m2 (stackPtr s - 24) (s.regValue .r12)
  have f3 : RamWriteFrame s.external m3 [stack s] := f2.memStore _
    ⟨_, List.mem_cons_self, Common.stackRange (off := 24) call.stackAvailable (by decide) (by decide)⟩
  have g4 := guard f3 32 6 1 (by decide) (by decide)
  let m4 := memStore m3 (stackPtr s - 32) (s.regValue .rbx)
  have f4 : RamWriteFrame s.external m4 [stack s] := f3.memStore _
    ⟨_, List.mem_cons_self, Common.stackRange (off := 32) call.stackAvailable (by decide) (by decide)⟩
  have g5 := guard f4 544 36 5 (by decide) (by decide)
  exact entryBlock a h1 h2 h3 h4 h6 h7 h12 h14 h15 g1 rfl g2 rfl g3 rfl g4 rfl g5 rfl

end K256.Proofs.Verify.Wrapper
