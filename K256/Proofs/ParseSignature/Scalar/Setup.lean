import K256.Proofs.ParseSignature.Memory
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn107730.Frame
import K256.Proofs.LIR.Fn127d70.Frame
import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.ParseSignature.Scalar

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

def fillActivation (fr : Activation) (mem : Ram) : Activation :=
  { fr with original := mem, rsp := fr.rsp - 160, ret := 0x1077bf,
            rbx := fr.rdi, r14 := 1, rdi := fr.rsp - 80, rsi := 32,
            rdx := fr.rsp - 112, rcx := 4, r8 := 256 }

def fillResume : StackFrame Value Label signature Reg.count :=
  { target := .l1077bf, kept := #v[], arity := rfl, guard := some ⟨64, 0x1077bf⟩ }

def Saved (fr : Activation) (mem : Ram) : Prop :=
  ∀ (k r : Nat), (k, r) ∈ [(48, 3), (40, 12), (32, 13), (24, 14), (16, 15), (8, 5)] →
    memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r

structure FillEntry (code : CodeMap) (fr : Activation) (args : Values Value Reg.count)
    (mem : Ram) : Prop where
  atoms : Atom.All code args mem (Fn127d70.frameInfo.entryAtoms (fillActivation fr mem))
  frame : RamWriteFrame fr.original mem [fr.region]
  saved : Saved fr mem
  source : Readable mem (fr.rsp - 80) 32
  dest : Writable code mem (fr.rsp - 112) 32
  sourceOutside : Outside [callStack (fillActivation fr mem)] (fr.rsp - 80) 32
  destOutside : Outside [callStack (fillActivation fr mem)] (fr.rsp - 112) 32
  separate : Outside [buffer (fr.rsp - 112) 32] (fr.rsp - 80) 32
  slot : Outside [buffer (fr.rsp - 112) 32] 0x203dd0 8
  words : ∀ i < 4, scalarWord mem (fr.rsp - 80) i = scalarWord fr.original fr.rsi i

set_option maxHeartbeats 800000 in
theorem setup_fill {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code) (fr : Activation)
    (args : Values Value Reg.count) (hentry : Atom.All code args fr.original (Fn107730.frameInfo.entryAtoms fr))
    (hn : fr.rdx = 32) (hr : Readable fr.original fr.rsi 32)
    (hin : Outside [callStack fr] fr.rsi 32) :
    ∃ (setup : Location Value Ram Label signature) (fillArgs : Values Value Reg.count) (mem : Ram),
      program.runBlock (dialect code) ⟨.l107730, args, fr.original⟩ = .jump setup ∧
      program.runBlock (dialect code) setup = .call ⟨.l127d70, fillArgs, mem⟩ fillResume ∧
      FillEntry code fr fillArgs mem := by
  change Atom.All code args fr.original (Fn107730.frameAt .l107730 fr) at hentry
  simp only [Fn107730.frameAt, Fn107730.frameAtG0, Atom.All, Atom.Holds] at hentry
  rcases hentry with ⟨hsp, hdf, _, hdx, hbx, hbp, hsi, hdi, _, h9, h12, h13, h14, h15,
    hmxcsr, hftw, hfcw, hread, _, _, hw, hroom, halign, hgot₁, hv₁, hgot₂, hv₂,
    hgot₃, hv₃, hapart, _⟩
  change Writable code fr.original (fr.rsp - 368) 368 at hw
  change fr.low.toNat + 368 ≤ fr.rsp.toNat at hroom
  change fr.rsp.toNat % 16 = 8 at halign
  change 0x203f98 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at hapart
  have stackAddr (k : Nat) (hk : k ≤ 368) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hk' : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hk']; omega), hk']
  have addr160 : (fr.rsp - 160).toNat = fr.rsp.toNat - 160 := stackAddr 160 (by decide)
  have addr368 : (fr.rsp - 368).toNat = fr.rsp.toNat - 368 := stackAddr 368 (by decide)
  have top := hread.low
  let stores := [buffer (fr.rsp - 160) 160]
  have inside (off width : Nat) (hoff : off ≤ 160) (hwidth : width ≤ off) :
      InRegions stores (fr.rsp - BitVec.ofNat 64 off) width := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (fr.rsp - 160).toNat ≤ _ ∧ _ + width ≤ (fr.rsp - 160).toNat + 160 ∧
      _ + width ≤ 2 ^ 64
    rw [stackAddr off (by omega), addr160]
    omega
  have stackWritable {m : Ram} (hf : RamWriteFrame fr.original m stores)
      (off width : Nat) (hoff : off ≤ 368) (hwidth : width ≤ off) :
      Writable code m (fr.rsp - BitVec.ofNat 64 off) width := by
    apply (hw.of_frame hf).sub <;> rw [stackAddr off hoff, addr368] <;> omega
  have stackGuard {m : Ram} (hf : RamWriteFrame fr.original m stores)
      (off width : Nat) (hoff : off ≤ 368) (hwidth : width ≤ off)
      {p : BitVec 64} {bytes : List UInt8} (cover : ∀ x ∈ codeRange p bytes, x ∈ fnCode)
      (pcOffset insn : Nat) (hinsn : pcOffset + insn ≤ bytes.length) :
      StoreOk code m (fr.rsp - BitVec.ofNat 64 off) width (p + BitVec.ofNat 64 pcOffset) insn := by
    exact storeOk_of_codeRange (stackWritable hf off width hoff hwidth)
      (fun x hx => hcode x (cover x hx)) hinsn
  have stackStore {m : Ram} (hf : RamWriteFrame fr.original m stores)
      (off : Nat) {width : Nat} (value : BitVec width)
      (hoff : off ≤ 160) (hwidth : width / 8 ≤ off) :
      RamWriteFrame fr.original (memStore m (fr.rsp - BitVec.ofNat 64 off) value) stores :=
    hf.memStore value (inside off (width / 8) hoff hwidth)
  have f0 : RamWriteFrame fr.original fr.original stores := .refl _ _
  have g1 : StoreOk code fr.original (fr.rsp - 8) 8 0x107730 1 :=
    stackGuard f0 8 8 (by decide) (by decide) code_l107730 0 1 (by decide)
  let m1 := memStore fr.original (fr.rsp - 8) fr.rbp
  have f1 : RamWriteFrame fr.original m1 stores := stackStore f0 8 fr.rbp (by decide) (by decide)
  have g2 : StoreOk code m1 (fr.rsp - 16) 8 0x107731 2 :=
    stackGuard f1 16 8 (by decide) (by decide) code_l107730 1 2 (by decide)
  let m2 := memStore m1 (fr.rsp - 16) fr.r15
  have f2 : RamWriteFrame fr.original m2 stores := stackStore f1 16 fr.r15 (by decide) (by decide)
  have g3 : StoreOk code m2 (fr.rsp - 24) 8 0x107733 2 :=
    stackGuard f2 24 8 (by decide) (by decide) code_l107730 3 2 (by decide)
  let m3 := memStore m2 (fr.rsp - 24) fr.r14
  have f3 : RamWriteFrame fr.original m3 stores := stackStore f2 24 fr.r14 (by decide) (by decide)
  have g4 : StoreOk code m3 (fr.rsp - 32) 8 0x107735 2 :=
    stackGuard f3 32 8 (by decide) (by decide) code_l107730 5 2 (by decide)
  let m4 := memStore m3 (fr.rsp - 32) fr.r13
  have f4 : RamWriteFrame fr.original m4 stores := stackStore f3 32 fr.r13 (by decide) (by decide)
  have g5 : StoreOk code m4 (fr.rsp - 40) 8 0x107737 2 :=
    stackGuard f4 40 8 (by decide) (by decide) code_l107730 7 2 (by decide)
  let m5 := memStore m4 (fr.rsp - 40) fr.r12
  have f5 : RamWriteFrame fr.original m5 stores := stackStore f4 40 fr.r12 (by decide) (by decide)
  have g6 : StoreOk code m5 (fr.rsp - 48) 8 0x107739 1 :=
    stackGuard f5 48 8 (by decide) (by decide) code_l107730 9 1 (by decide)
  let m6 := memStore m5 (fr.rsp - 48) fr.rbx
  have f6 : RamWriteFrame fr.original m6 stores := stackStore f5 48 fr.rbx (by decide) (by decide)
  have rsp : Value.get 64 args[4] = fr.rsp := congrArg (Value.get 64) hsp
  have rdx : Value.get 64 args[2] = 32 := (congrArg (Value.get 64) hdx).trans hn
  have rbp : Value.get 64 args[5] = fr.rbp := congrArg (Value.get 64) hbp
  have r15 : Value.get 64 args[15] = fr.r15 := congrArg (Value.get 64) h15
  have r14 : Value.get 64 args[14] = fr.r14 := congrArg (Value.get 64) h14
  have r13 : Value.get 64 args[13] = fr.r13 := congrArg (Value.get 64) h13
  have r12 : Value.get 64 args[12] = fr.r12 := congrArg (Value.get 64) h12
  have rbx : Value.get 64 args[3] = fr.rbx := congrArg (Value.get 64) hbx
  have rdi : Value.get 64 args[7] = fr.rdi := congrArg (Value.get 64) hdi
  have rsi : Value.get 64 args[6] = fr.rsi := congrArg (Value.get 64) hsi
  have inputLoad {m : Ram} (hf : RamWriteFrame fr.original m stores)
      (off : Nat) (hoff : off + 8 ≤ 32) :
      let a := fr.rsi + BitVec.ofNat 64 off
      LoadOk m a 8 ∧ memLoad m a 64 = memLoad fr.original a 64 := by
    intro a
    have hlow := hr.low
    have ha : a.toNat = fr.rsi.toNat + off := by
      dsimp only [a]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨LoadOk.of_region (hr.of_frame hf) (by rw [ha]; omega)
      (by rw [ha]; omega), hf.memLoad_eq ?_⟩
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r h
    rcases List.mem_singleton.mp h with rfl
    have apart := hin.2 _ (List.mem_singleton_self _)
    change fr.rsi.toNat + 32 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat at apart
    change a.toNat + 8 ≤ (fr.rsp - 160).toNat ∨
      (fr.rsp - 160).toNat + 160 ≤ a.toNat
    rw [ha, addr160]
    omega
  have load24 :
      LoadOk m6 (fr.rsi + 24) 8 ∧
      memLoad m6 (fr.rsi + 24) 64 = memLoad fr.original (fr.rsi + 24) 64 :=
    inputLoad f6 24 (by decide)
  have l24 : LoadOk m6 (fr.rsi + 24) 8 := load24.1
  have v24 : memLoad m6 (fr.rsi + 24) 64 = memLoad fr.original (fr.rsi + 24) 64 := load24.2
  have g7 : StoreOk code m6 (fr.rsp - 56) 8 0x107755 5 :=
    stackGuard f6 56 8 (by decide) (by decide) code_l107751 4 5 (by decide)
  let m7 := memStore m6 (fr.rsp - 56) (memLoad fr.original (fr.rsi + 24) 64)
  have f7 : RamWriteFrame fr.original m7 stores :=
    stackStore f6 56 (memLoad fr.original (fr.rsi + 24) 64) (by decide) (by decide)
  have load16 :
      LoadOk m7 (fr.rsi + 16) 8 ∧
      memLoad m7 (fr.rsi + 16) 64 = memLoad fr.original (fr.rsi + 16) 64 :=
    inputLoad f7 16 (by decide)
  have l16 : LoadOk m7 (fr.rsi + 16) 8 := load16.1
  have v16 : memLoad m7 (fr.rsi + 16) 64 = memLoad fr.original (fr.rsi + 16) 64 := load16.2
  have g8 : StoreOk code m7 (fr.rsp - 64) 8 0x10775e 5 :=
    stackGuard f7 64 8 (by decide) (by decide) code_l107751 13 5 (by decide)
  let m8 := memStore m7 (fr.rsp - 64) (memLoad fr.original (fr.rsi + 16) 64)
  have f8 : RamWriteFrame fr.original m8 stores :=
    stackStore f7 64 (memLoad fr.original (fr.rsi + 16) 64) (by decide) (by decide)
  have load0 :
      LoadOk m8 fr.rsi 8 ∧ memLoad m8 fr.rsi 64 = memLoad fr.original fr.rsi 64 := by
    simpa only [BitVec.add_zero] using inputLoad f8 0 (by decide)
  have l0 : LoadOk m8 fr.rsi 8 := load0.1
  have v0 : memLoad m8 fr.rsi 64 = memLoad fr.original fr.rsi 64 := load0.2
  have load8 :
      LoadOk m8 (fr.rsi + 8) 8 ∧
      memLoad m8 (fr.rsi + 8) 64 = memLoad fr.original (fr.rsi + 8) 64 :=
    inputLoad f8 8 (by decide)
  have l8 : LoadOk m8 (fr.rsi + 8) 8 := load8.1
  have v8 : memLoad m8 (fr.rsi + 8) 64 = memLoad fr.original (fr.rsi + 8) 64 := load8.2
  have g9 : StoreOk code m8 (fr.rsp - 72) 8 0x10776a 5 :=
    stackGuard f8 72 8 (by decide) (by decide) code_l107751 25 5 (by decide)
  let m9 := memStore m8 (fr.rsp - 72) (memLoad fr.original (fr.rsi + 8) 64)
  have f9 : RamWriteFrame fr.original m9 stores :=
    stackStore f8 72 (memLoad fr.original (fr.rsi + 8) 64) (by decide) (by decide)
  have g10 : StoreOk code m9 (fr.rsp - 80) 8 0x10776f 5 :=
    stackGuard f9 80 8 (by decide) (by decide) code_l107751 30 5 (by decide)
  let m10 := memStore m9 (fr.rsp - 80) (memLoad fr.original fr.rsi 64)
  have f10 : RamWriteFrame fr.original m10 stores :=
    stackStore f9 80 (memLoad fr.original fr.rsi 64) (by decide) (by decide)
  have g11 : StoreOk code m10 (fr.rsp - 148) 4 0x107774 8 :=
    stackGuard f10 148 4 (by decide) (by decide) code_l107751 35 8 (by decide)
  let m11 := memStore m10 (fr.rsp - 148) (256 : BitVec 32)
  have f11 : RamWriteFrame fr.original m11 stores :=
    stackStore f10 148 (256 : BitVec 32) (by decide) (by decide)
  have g12 : StoreOk code m11 (fr.rsp - 88) 8 0x10777c 9 :=
    stackGuard f11 88 8 (by decide) (by decide) code_l107751 43 9 (by decide)
  let m12 := memStore m11 (fr.rsp - 88) (0 : BitVec 64)
  have f12 : RamWriteFrame fr.original m12 stores :=
    stackStore f11 88 (0 : BitVec 64) (by decide) (by decide)
  have g13 : StoreOk code m12 (fr.rsp - 96) 8 0x107785 9 :=
    stackGuard f12 96 8 (by decide) (by decide) code_l107751 52 9 (by decide)
  let m13 := memStore m12 (fr.rsp - 96) (0 : BitVec 64)
  have f13 : RamWriteFrame fr.original m13 stores :=
    stackStore f12 96 (0 : BitVec 64) (by decide) (by decide)
  have g14 : StoreOk code m13 (fr.rsp - 104) 8 0x10778e 9 :=
    stackGuard f13 104 8 (by decide) (by decide) code_l107751 61 9 (by decide)
  let m14 := memStore m13 (fr.rsp - 104) (0 : BitVec 64)
  have f14 : RamWriteFrame fr.original m14 stores :=
    stackStore f13 104 (0 : BitVec 64) (by decide) (by decide)
  have g15 : StoreOk code m14 (fr.rsp - 112) 8 0x107797 9 :=
    stackGuard f14 112 8 (by decide) (by decide) code_l107751 70 9 (by decide)
  let m15 := memStore m14 (fr.rsp - 112) (0 : BitVec 64)
  have f15 : RamWriteFrame fr.original m15 stores :=
    stackStore f14 112 (0 : BitVec 64) (by decide) (by decide)
  have g16 : StoreOk code m15 (fr.rsp - 160) 8 0x1077ba 5 :=
    stackGuard f15 160 8 (by decide) (by decide) code_l107751 105 5 (by decide)
  let m16 := memStore m15 (fr.rsp - 160) (0x1077bf : BitVec 64)
  have f16 : RamWriteFrame fr.original m16 stores :=
    stackStore f15 160 (0x1077bf : BitVec 64) (by decide) (by decide)
  refine ⟨?setup, ?fillArgs, m16, ?entryBlock, ?setupBlock, ?result⟩
  case entryBlock =>
    cfg_eval
    dsimp only [m1, m2, m3, m4, m5, Activation.original] at g1 g2 g3 g4 g5 g6
    simp only [g1, g2, g3, g4, g5, g6, rsp, rdx, rbp, r15, r14, r13, r12, rbx, rdi,
      cmpSpec_ZF, Bool.not_eq_true', beq_self_eq_true, ↓reduceIte, Bool.true_eq_false]
    rfl
  case setupBlock =>
    cfg_eval
    dsimp only [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,
      Activation.original] at g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 l24 l16 l0 l8 v24 v16 v0 v8
    simp only [rsi, l24, v24, l16, v16, l0, v0, l8, v8, g7, g8, g9, g10, g11,
      g12, g13, g14, g15, g16, ↓reduceIte]
    rfl
  case result =>
    have keepLoad (m : Ram) (off target : Nat) {width : Nat} (v : BitVec width)
        (hoff : off ≤ 160) (htarget : target ≤ 160) (hv : width / 8 ≤ off)
        (ht : 8 ≤ target)
        (hd : target + width / 8 ≤ off ∨ off + 8 ≤ target) :
        memLoad (memStore m (fr.rsp - BitVec.ofNat 64 off) v)
          (fr.rsp - BitVec.ofNat 64 target) 64 =
          memLoad m (fr.rsp - BitVec.ofNat 64 target) 64 := by
      apply memLoad_memStore_of_rangeApart
      apply RangeApart.of_toNat <;>
        simp only [stackAddr off (by omega), stackAddr target (by omega), Nat.reduceDiv] <;> omega
    have sameLoad (m : Ram) (a : BitVec 64) (v : BitVec 64) :
        memLoad (memStore m a v) a 64 = v :=
      memLoad_memStore_same m a v (by decide) (by decide)
    have gotOutside (a : BitVec 64) (ha : 0x203dd0 ≤ a.toNat)
        (hb : a.toNat + 8 ≤ 0x203e28) : Outside stores a 8 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change a.toNat + 8 ≤ (fr.rsp - 160).toNat ∨
        (fr.rsp - 160).toNat + 160 ≤ a.toNat
      rw [addr160]
      omega
    have roomFill : fr.low.toNat + 208 ≤ (fr.rsp - 160).toNat := by omega
    have alignFill : (fr.rsp - 160).toNat % 16 = 8 := by omega
    have apartFill : 0x203ef8 ≤ (fr.rsp - 160).toNat ∨
        (fr.rsp - 160).toNat ≤ 0x203dd0 := by omega
    have writeFill : Writable code m16 ((fr.rsp - 160) - 208) 208 := by
      rw [show fr.rsp - 160 - 208 = fr.rsp - 368 by bv_omega]
      exact stackWritable f16 368 208 (by decide) (by decide)
    have retFill : memLoad m16 (fr.rsp - 160) 64 = 0x1077bf := sameLoad _ _ _
    have outsideFill (mem : Ram) (off length : Nat) (hoff : off ≤ 152) (hlen : length ≤ off) :
        Outside [callStack (fillActivation fr mem)] (fr.rsp - BitVec.ofNat 64 off) length := by
      refine ⟨by rw [stackAddr off (by omega)]; omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change (fr.rsp - BitVec.ofNat 64 off).toNat + length ≤ fr.low.toNat ∨
        fr.low.toNat + ((fr.rsp - 160).toNat + 8 - fr.low.toNat) ≤
          (fr.rsp - BitVec.ofNat 64 off).toNat
      rw [addr160, stackAddr off (by omega)]
      omega
    have addr80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := stackAddr 80 (by decide)
    have addr112 : (fr.rsp - 112).toNat = fr.rsp.toNat - 112 := stackAddr 112 (by decide)
    refine ⟨?atoms, ?frame, ?saved, (stackWritable f16 80 32 (by decide) (by decide)).readable,
      stackWritable f16 112 32 (by decide) (by decide),
      outsideFill m16 80 32 (by decide) (by decide), outsideFill m16 112 32 (by decide) (by decide),
      ?separate, ?slot, ?words⟩
    case frame =>
      apply (RamWriteFrame.refl fr.original [fr.region]).trans f16
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change fr.low.toNat ≤ (fr.rsp - 160).toNat ∧
        (fr.rsp - 160).toNat + 160 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      rw [addr160]
      omega
    case saved =>
      intro off reg h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp (disch := decide) only [m16, m15, m14, m13, m12, m11, m10, m9,
          m8, m7, m6, m5, m4, m3, m2, m1, BitVec.ofNat_eq_ofNat, keepLoad, sameLoad, Activation.entryReg]
    case separate =>
      refine ⟨by omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change _ ≤ (fr.rsp - 112).toNat ∨ (fr.rsp - 112).toNat + 32 ≤ _
      omega
    case slot =>
      refine ⟨by decide, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change 0x203dd8 ≤ (fr.rsp - 112).toNat ∨ (fr.rsp - 112).toNat + 32 ≤ 0x203dd0
      omega
    case words =>
      have addr (i : Nat) (hi : i < 4) :
          fr.rsp - 80 + BitVec.ofNat 64 (8 * (3 - i)) =
            fr.rsp - BitVec.ofNat 64 (80 - 8 * (3 - i)) := by
        have h : 80 - 8 * (3 - i) + 8 * (3 - i) = 80 := by omega
        have hv := congrArg (BitVec.ofNat 64) h
        rw [BitVec.ofNat_add] at hv
        change BitVec.ofNat 64 (80 - 8 * (3 - i)) + BitVec.ofNat 64 (8 * (3 - i)) = 80 at hv
        bv_omega
      intro i hi
      simp only [scalarWord, addr i hi]
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;>
        simp (disch := decide) only [m16, m15, m14, m13, m12, m11, m10, m9, m8, m7,
          Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat, keepLoad, sameLoad, BitVec.add_zero]
    case atoms =>
      have fillRead : Readable m16 (fr.rsp - 160) 8 := (stackWritable f16 160 8 (by decide) (by decide)).readable
      have got₁ := hgot₁.of_frame f16
      have got₂ := hgot₂.of_frame f16
      have got₃ := hgot₃.of_frame f16
      have gotv₁ := (f16.memLoad_eq (gotOutside 0x203dd0 (by decide) (by decide))).trans hv₁
      have gotv₂ := (f16.memLoad_eq (gotOutside 0x203de0 (by decide) (by decide))).trans hv₂
      have gotv₃ := (f16.memLoad_eq (gotOutside 0x203e20 (by decide) (by decide))).trans hv₃
      change Atom.All code _ m16 (Fn127d70.frameAt .l127d70 (fillActivation fr m16))
      simp only [Fn127d70.frameAt, Fn127d70.frameAtG0, Atom.All, Atom.Holds, fillActivation]
      exact ⟨rfl, hdf, rfl, rfl, rfl, hbp,
        rfl, rfl, rfl, h9, h12, h13, rfl, h15, hmxcsr, hftw, hfcw,
        fillRead, retFill, by decide, writeFill, roomFill, alignFill, got₁, gotv₁,
        got₂, gotv₂, got₃, gotv₃, apartFill, trivial⟩

end K256.Proofs.ParseSignature.Scalar
