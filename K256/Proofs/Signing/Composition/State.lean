import K256.Proofs.Signing.Nonce.Start.State
import K256.Proofs.Signing.Execution
import K256.Proofs.Signing.LIR.Program

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers)
open Verify.Hash

abbrev State := Standards.RFC.DeterministicSigning.Nonce.State
abbrev sp (s : RamState) := stackPtr s - 1288
abbrev Reach := (LIR.program.sem (dialect Extracted.programImage)).Reaches
abbrev resume (l : LIR.Label) (addr : BitVec 64) : StackFrame Value LIR.Label (fun _ => Reg.count) Reg.count :=
  ⟨l, #v[], rfl, some ⟨64,addr⟩⟩
abbrev core (l : LIR.Label) (a : Registers) (m : Ram) : LIR.lifted.State :=
  ⟨⟨l,a,m⟩,[resume .l102795 0x102795]⟩
abbrev fill (l : LIR.Label) (a : Registers) (m : Ram) : LIR.lifted.State :=
  ⟨⟨l,a,m⟩,[resume .l1058d0 0x1058d0,resume .l102795 0x102795]⟩

structure Memory (s : RamState) (m : Ram) : Prop where
  written : RamWriteFrame s.external m [Stack.region s signingKeyTrySign.minStackBytes]
  ret : memLoad m (stackPtr s) 64 = (returnBoundary s).rip
  savedWrapperRBX : memLoad m (stackPtr s-32) 64 = s.regValue .rbx
  savedWrapperR12 : memLoad m (stackPtr s-24) 64 = s.regValue .r12
  savedWrapperR14 : memLoad m (stackPtr s-16) 64 = s.regValue .r14
  savedWrapperR15 : memLoad m (stackPtr s-8) 64 = s.regValue .r15

structure KeyMemory (s : RamState) (d : Nat) (m : Ram) : Prop extends Memory s m where
  key : WordsAt m (sp s+1016) 64 (scalarWords d)
  coreReturn : memLoad m (sp s+808) 64 = 0x102795

structure CoreMemory (s : RamState) (d : Nat) (m : Ram) : Prop extends KeyMemory s d m where
  keyPtr : memLoad m (sp s+344) 64 = sp s+1016
  resultPtr : memLoad m (sp s+416) 64 = sp s+888
  savedOutput : memLoad m (sp s+760) 64 = s.regValue .rdi
  savedR13 : memLoad m (sp s+776) 64 = s.regValue .r13
  savedRbp : memLoad m (sp s+800) 64 = s.regValue .rbp

structure Descriptor (s : RamState) (msg : ByteArray) (m : Ram) : Prop where
  pointer : memLoad m (sp s+1136) 64 = s.regValue .rdx
  size : memLoad m (sp s+1144) 64 = BitVec.ofNat 64 msg.size

structure CoreEntry (s : RamState) (d : Nat) (msg : ByteArray) (a : Registers) (m : Ram) : Prop
    extends KeyMemory s d m, Descriptor s msg m where
  rsp : a[4] = ⟨64,sp s+808⟩
  dst : a[7] = ⟨64,sp s+888⟩
  secret : a[6] = ⟨64,sp s+1016⟩
  descriptor : a[2] = ⟨64,sp s+1136⟩
  count : a[1] = ⟨64,1⟩
  output : a[3] = ⟨64,s.regValue .rdi⟩
  framePtr : a[5] = ⟨64,s.regValue .rbp⟩
  r13 : a[13] = ⟨64,s.regValue .r13⟩
  df : a[22] = ⟨1,0⟩
  savedWidths : ∀ i : Fin Reg.count, i.val ∈ [12,14,15] → a[i].width = 64
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16

structure HashEntry (s : RamState) (d : Nat) (msg : ByteArray) (a : Registers) (m : Ram) : Prop
    extends CoreMemory s d m, Descriptor s msg m where
  rsp : a[4] = ⟨64,sp s⟩
  df : a[22] = ⟨1,0⟩
  count : a[1] = ⟨64,1⟩
  descriptor : a[2] = ⟨64,sp s+1136⟩
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16
  iv : Verify.Hash.Compression.StateAt m (sp s+552) initialHash
  buffered : memLoad m (sp s+551) 8 = 0
  blocks : memLoad m (sp s+584) 64 = 0

structure Digest (s : RamState) (d : Nat) (msg : ByteArray) (a : Registers) (m : Ram) : Prop
    extends CoreMemory s d m where
  rsp : a[4] = ⟨64,sp s⟩
  df : a[22] = ⟨1,0⟩
  r13 : a[13] = ⟨64,sp s+256⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,14,15] → a[i].width = 64
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16
  hash : Verify.Hash.Compression.StateAt m (sp s+72) (compressBlocks initialHash (bytePadding msg))

structure Outer (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (a : Registers) (m : Ram) : Prop
    extends CoreMemory s d m, Nonce.CandidateRegisters a (sp s) where
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16
  hash : (⟨(sp s+352).toNat,32⟩ : MemoryRegion).HasBytes m (SHA256.hashBytes msg)
  order : WordsAt m (sp s+592) 64 (scalarWords domain.n)
  orderPtr : memLoad m (sp s+688) 64 = sp s+592
  state : Nonce.Initialize.StateAt m (sp s+696) st

structure Result (s : RamState) (pair : Nat × Nat) (a : Registers) (m : Ram) : Prop
    extends Memory s m where
  rsp : a[4] = ⟨64,sp s+816⟩
  dst : a[3] = ⟨64,s.regValue .rdi⟩
  rbp : a[5] = ⟨64,s.regValue .rbp⟩
  r13 : a[13] = ⟨64,s.regValue .r13⟩
  df : a[22] = ⟨1,0⟩
  tag : memLoad m (sp s+888) 64 = 0
  r : WordsAt m (sp s+896) 64 (scalarWords pair.1)
  lowS : WordsAt m (sp s+928) 64
    (scalarWords (if pair.2 > domain.n / 2 then domain.n - pair.2 else pair.2))

structure FillRun (s : RamState) (d : Nat) (msg : ByteArray)
    (head : State → Registers → Ram → Prop) : Prop where
  inRange : ∀ {st a m}, head st a m → let k := (candidate st).1
    0 < k → k < domain.n → ∃ b n, Reach (fill .l100ab0 a m) (core .l1058d0 b n) ∧
      Outer s d msg (retry st) b n ∧
      (⟨(sp s+384).toNat,32⟩ : MemoryRegion).HasBytes n (Encoding.natToOctets 32 k)
  outOfRange : ∀ {st a m}, head st a m → ¬ (0 < (candidate st).1 ∧ (candidate st).1 < domain.n) →
    ∃ b n c t, Reach (fill .l100ab0 a m) (fill .l100ac0 b n) ∧
      Reach (fill .l100ac0 b n) (fill .l100ab0 c t) ∧ head (retry st) c t

def AtCandidate (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (x : LIR.lifted.State) : Prop :=
  ∃ head : State → Registers → Ram → Prop, ∃ a m, x = fill .l100ab0 a m ∧ head st a m ∧ FillRun s d msg head

end K256.Proofs.Signing.Composition
