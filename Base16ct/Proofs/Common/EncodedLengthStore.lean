import Base16ct.Spec.Program
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Effect
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StorePreAny (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64)
    (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  low : (addr s).toNat + len ≤ 2^32
  mem : ∀ i, i < len → (s.external[addr s + BitVec.ofNat 64 i]?).isSome
  tables : (addr s).toNat + len ≤ 0x1000 ∨ 0x3000 ≤ (addr s).toNat
  code : RangeApart (addr s) len p codeLen

theorem mov_rsi_store_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StorePreAny p 3 (fun s => s.regValue .rdx) 8)
      (codeRange p [0x48, 0x89, 0x32])
      (storeEffect p 3 (fun s => s.regValue .rdx)
        (fun s => (Operand.reg 6 : Operand 64).read s)) := by
  let am : AddrMode := .base 2 .none
  have ham : am.modrm 6 = 0x32 := by decide +kernel
  have htail : am.tail.length = 0 := by decide +kernel
  have htail0 : am.tail = [] := by decide +kernel
  have haddr : ∀ s : RamState, am.addrAt s 3 = s.regValue .rdx := by
    intro s
    dsimp [am, AddrMode.addrAt, AddrMode.addr, AddrMode.reg64, Disp.value]
    change (Operand.reg (2#5) : Operand 64).read s + (0#64) = s.regValue .rdx
    rw [BitVec.add_zero]
    change s.GPR[2] = s.GPR[2]
    rfl
  have hstoreAddr : ∀ s : RamState, storeAddrAt p am 3 s = am.addrAt s 3 := by
    intro s
    unfold storeAddrAt
    exact AddrMode.addr_of_gpr rfl _
  have haddrstore :
      (fun s : RamState => storeAddrAt p am 3 s) =
        (fun s : RamState => am.addrAt s 3) := by
    funext s
    exact hstoreAddr s
  have hgen := Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step
    (p := p) (rex := 0x48)
    (by unfold RexWPrefix; decide +kernel) (reg := 6) (am := am)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hgen' : StepEffect (Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre
      p 3
      (fun s => am.addrAt s 3) 8)
      (codeRange p [0x48, 0x89, 0x32])
      (movM64R64Effect p 6 am) := by
    simp only [htail, htail0, List.length_nil, Nat.add_zero, ham,
      show gprNumber 0 (rexR (0x48 : UInt8).toBitVec) (6 : BitVec 3) = 6 by decide +kernel] at hgen
    simpa only [haddrstore] using hgen
  intro s h hcode hpre
  obtain ⟨hp, hlow, hmem, htables, hcodeApart⟩ := hpre
  have hpre' : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre
      p 3 (fun s => am.addrAt s 3) 8 s := by
    refine ⟨hp, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [haddr s] using hlow
      · intro i hi
        simpa [haddr s] using hmem i hi
      · intro i hi x
        have ha : (am.addrAt s 3).toNat = (s.regValue .rdx).toNat := by
          rw [haddr]
        have htables' := htables
        rw [← haddr s] at htables'
        rcases htables' with ht | ht
        · simp [Base16ct.Proofs.Copied.Md5.Spec.Program.InPageTables,
            MemoryRegion.Contains, BitVec.toNat_add,
            Nat.mod_eq_of_lt (show (am.addrAt s 3).toNat + i < 2^64 by rw [ha]; omega)] at x ⊢
          omega
        · simp [Base16ct.Proofs.Copied.Md5.Spec.Program.InPageTables,
            MemoryRegion.Contains, BitVec.toNat_add,
            Nat.mod_eq_of_lt (show (am.addrAt s 3).toNat + i < 2^64 by rw [ha]; omega)] at x ⊢
          omega
    · simpa [haddr s] using hcodeApart
  have h := hgen' s h hcode hpre'
  simpa only [movM64R64Effect, haddrstore, haddr, htail,
    show gprNumber 0 (rexR (0x48 : UInt8).toBitVec) (6 : BitVec 3) = 6 by decide +kernel] using h

end Base16ct.Proofs.Common
