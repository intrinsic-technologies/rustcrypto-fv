import K256.Proofs.Verify.Core.Signature.Nonzero

namespace K256.Proofs.Verify.Core.Components

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Generate.Generator.Multiply (scalarWords)
abbrev Word := BitVec 64

structure Fixed (fr : Activation) (a : Registers) : Prop where
  bx : a[3] = ⟨64,fr.rdi⟩
  bp : a[5] = ⟨64,fr.rbp⟩
  r12 : a[12] = ⟨64,fr.rdx⟩
  r13 : a[13] = ⟨64,fr.rcx⟩
  r14 : a[14] = ⟨64,fr.rsi⟩
  r15 : a[15] = ⟨64,fr.r8⟩
  df : a[22] = ⟨1,0⟩
  mx : a[39] = ⟨32,fr.mxcsr⟩
  ft : a[50] = ⟨16,fr.ftw⟩
  fc : a[51] = ⟨16,fr.fcw⟩

structure Arguments (fr : Activation) (b : Registers) : Prop extends Fixed fr b where
  sp : b[4] = ⟨64, localSp fr - 8⟩
  si : b[6] = ⟨64, localSp fr + 8⟩
  di : b[7] = ⟨64, localSp fr + 136⟩
  cx : b[1].width = 64
  dx : b[2].width = 64
  r8 : b[8].width = 64
  r9 : b[9].width = 64

def stage (m : Ram) (sp ret : Word) (w : Vector Word 4) : Ram :=
  let m := memStore m (sp + 160) w[3]
  let m := memStore m (sp + 152) w[2]
  let m := memStore m (sp + 144) w[1]
  let m := memStore m (sp + 136) w[0]
  let m := memStore m (sp + 32) (0 : Word)
  let m := memStore m (sp + 24) (0 : Word)
  let m := memStore m (sp + 16) (0 : Word)
  let m := memStore m (sp + 8) (0 : Word)
  memStore m (sp - 8) ret

def saveRegs (fr : Activation) (sp : Word) : Ram :=
  let m := memStore fr.original (sp + 480) fr.r15
  let m := memStore m (sp + 472) fr.r14
  let m := memStore m (sp + 464) fr.r13
  let m := memStore m (sp + 456) fr.r12
  memStore m (sp + 448) fr.rbx

def saveR (m : Ram) (sp : Word) (w : Vector Word 4) : Ram :=
  let m := memStore m (sp + 256) w[0]
  let m := memStore m (sp + 264) w[1]
  let m := memStore m (sp + 272) w[2]
  memStore m (sp + 280) w[3]

structure Loads (m : Ram) (addr : Word) (off : Nat) (w : Vector Word 4) : Prop where
  w0 : memLoad m (addr + BitVec.ofNat 64 off) 64 = w[0]
  w1 : memLoad m (addr + BitVec.ofNat 64 (off+8)) 64 = w[1]
  w2 : memLoad m (addr + BitVec.ofNat 64 (off+16)) 64 = w[2]
  w3 : memLoad m (addr + BitVec.ofNat 64 (off+24)) 64 = w[3]

theorem wordsToLoads {m : Ram} {sp : Word} {off : Nat} {w : Vector Word 4}
    (h : WordsAt m (sp + BitVec.ofNat 64 off) 64 w) : Loads m sp off w := by
  have load (i : Nat) (hi : i < 4) := h i hi
  simp only [wordAddr,Nat.reduceDiv,BitVec.add_assoc,← BitVec.ofNat_add] at load
  exact ⟨by simpa using load 0 (by decide),load 1 (by decide),load 2 (by decide),load 3 (by decide)⟩

end K256.Proofs.Verify.Core.Components
