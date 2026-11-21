import Sha2.Proofs.Wrapper.Absorb.State
import Sha2.Proofs.Wrapper.Absorb.ByteAdd
import Sha2.Proofs.Wrapper.Absorb.Memory
import Sha2.Proofs.Wrapper.Absorb.SmallSetup
import Sha2.Proofs.Wrapper.Absorb.TailLength

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

set_option maxHeartbeats 800000 in
theorem short {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : SliceState (v := v) initial s inputs index)
    (rip : s.RIP=(v.pc 0xa0))
    (small : (inputs[index]'input.remaining).bytes.size < 64-(prefixMessage inputs index).size%64) :
    ∃ t, Buffered (v := v) initial t (prefixMessage inputs (index+1)) ∧ t.RIP=(v.pc 0xc1) ∧
      t.regValue .r14=BitVec.ofNat 64 index ∧ t.regValue .r15=BitVec.ofNat 64 inputs.size := by
  let i : Fin inputs.size := ⟨index,input.remaining⟩
  have bound : (prefixMessage inputs index).size%64 + inputs[i].bytes.size < 64 := by
    change (prefixMessage inputs index).size%64 + (inputs[index]'input.remaining).bytes.size < 64
    omega
  have outside := (validCall_returnBoundary ctx.machine ctx.call).2.2
  obtain ⟨fuel,b,run,ready,_,setup⟩ := SmallSetup.run (returnBoundary initial) outside s
    (supportedMachine_readyToStep input.machine) (SmallSetup.code input.loaded) rip
  have frameB : AgreesExcept [.reg 7,.reg 6,.reg 2,.flags,.rip] s b := setup.agrees
  have bufferedB := buffered_of_agrees ctx input.toBuffered run ready frameB
    (by simp [Component.Covers]) (by simp)
  have destinationB : b.regValue .rdi=stackPtr initial-152+BitVec.ofNat 64 ((prefixMessage inputs index).size%64) := by
    have write : b.regValue .rdi = rspOf s + s.regValue .r12 + (192#64) := setup.writes.1
    rw [write,input.position,BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 ((prefixMessage inputs index).size%64)) (192#64),
      ← BitVec.add_assoc,stack_address input.rsp]
    rfl
  have sourceB : b.regValue .rsi=inputs[i].address+BitVec.ofNat 64 0 := by
    have write : b.regValue .rsi=s.regValue .r13 := setup.writes.2.1
    change b.regValue .rsi=(inputs[index]'input.remaining).address+(0#64)
    rw [BitVec.add_zero]
    exact write.trans input.source
  have countB : b.regValue .rdx=BitVec.ofNat 64 inputs[i].bytes.size := setup.writes.2.2.trans input.length
  obtain ⟨c,copy⟩ := Copy.copy ctx bufferedB.toPreserved .short i (offset:=0)
    (by omega) (Nat.le_of_lt bound) setup.rip destinationB sourceB countB
  have tailC := copied_tail ctx bufferedB copy (Nat.le_refl _) (Nat.le_of_lt bound)
  have hashC := hashState_of_bytes bufferedB.hashWords
    (copy.bytes_unchanged ctx (Nat.le_of_lt bound) (offset:=88) (len:=32)
      (by decide) (by decide) (.inr (by omega)))
  have blocksC : memLoad c.external (stackPtr initial-56) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs index).size/64) := by
    rw [← bufferedB.blocks]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    exact copy.bytes_unchanged ctx (Nat.le_of_lt bound) (offset:=56) (len:=8)
      (by decide) (by decide) (.inr (by omega)) j hj
  have rbxC : c.regValue .rbx=BitVec.ofNat 64 inputs[i].bytes.size :=
    (copy.abi.1 .rbx (by simp)).trans
      ((frameB.read (n:=64) (r:=3) (by simp)).trans input.length)
  have r12C : c.regValue .r12=BitVec.ofNat 64 ((prefixMessage inputs index).size%64) :=
    (copy.abi.1 .r12 (by simp)).trans
      ((frameB.read (n:=64) (r:=12) (by simp)).trans input.position)
  obtain ⟨d,preservedD,ripD,lowD,frameD⟩ := add_short_length ctx copy.preserved (copy.rip.trans (by cases v <;> rfl))
  have lengthD : (Operand.reg 3 : Operand 8).read d =
      BitVec.ofNat 8 ((prefixMessage inputs index).size%64+inputs[i].bytes.size) := by
    rw [lowD]
    change (c.regValue .rbx).setWidth 8 + (c.regValue .r12).setWidth 8 = _
    rw [rbxC,r12C,BitVec.setWidth_ofNat_of_le (by decide),BitVec.setWidth_ofNat_of_le (by decide),← BitVec.ofNat_add,Nat.add_comm]
  obtain ⟨t,preservedT,ripT,lengthT,frameT⟩ := store_length ctx preservedD false ripD
  have noMemD : ∀ a, d.external[a]?=c.external[a]? :=
    fun a => frameD.memory a (by simp [Component.Covers])
  have hashD := hashState_of_bytes hashC (fun j _ => noMemD _)
  have hashT := hashState_of_bytes hashD (store_bytes (offset:=88) (len:=32) frameT
    (by unfold OffsetsApart; decide +kernel) (by decide))
  have tailSize : (remainderBytes (prefixMessage inputs index) ++ inputs[i].bytes).size =
      (prefixMessage inputs index).size%64+inputs[i].bytes.size := by
    rw [ByteArray.size_append,remainderBytes_size]
  have tailC' : (⟨(stackPtr initial-152).toNat,
      (remainderBytes (prefixMessage inputs index) ++ inputs[i].bytes).size⟩ : MemoryRegion).HasBytes
      c.external (remainderBytes (prefixMessage inputs index) ++ inputs[i].bytes) := by
    simpa only [ByteArray.extract_zero_size] using tailC
  have tailT : (⟨(stackPtr initial-152).toNat,
      (remainderBytes (prefixMessage inputs index) ++ inputs[i].bytes).size⟩ : MemoryRegion).HasBytes
      t.external (remainderBytes (prefixMessage inputs index) ++ inputs[i].bytes) := by
    refine ⟨rfl,fun j => ?_⟩
    have hj : j.val < (prefixMessage inputs index).size%64+inputs[i].bytes.size := by
      simpa only [tailSize] using j.isLt
    have changed := store_bytes (offset:=152)
      (len:=(prefixMessage inputs index).size%64+inputs[i].bytes.size) frameT
      (by change 1 ≤ 18446744073709551553 ∧ _ ≤ 63; constructor <;> omega) (by omega) j.val hj
    have old := tailC'.2 j
    change c.external[BitVec.ofNat 64 ((stackPtr initial-152#64).toNat+j.val)]? = _ at old
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at old
    change t.external[BitVec.ofNat 64 ((stackPtr initial-152#64).toNat+j.val)]? = _
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    exact changed.trans ((noMemD _).trans old)
  have countT : memLoad t.external (stackPtr initial-56) 64 =
      BitVec.ofNat 64 ((prefixMessage inputs index).size/64) := by
    rw [← blocksC]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    exact (store_bytes (offset:=56) (len:=8) frameT
      (by unfold OffsetsApart; decide +kernel) (by decide) j hj).trans (noMemD _)
  have result : Buffered (v := v) initial t (prefixMessage inputs index ++ inputs[i].bytes) := by
    have small' : inputs[i].bytes.size < 64-(prefixMessage inputs index).size%64 := small
    have counts := append_short_counts (prefixMessage inputs index) inputs[i].bytes small'
    refine ⟨preservedT,?_,?_,?_,?_⟩
    · rw [compressBlocks_append_short _ _ _ small']
      exact hashT
    · change (⟨(stackPtr initial-152).toNat, _⟩ : MemoryRegion).HasBytes t.external
        (remainderBytes (prefixMessage inputs index ++ inputs[i].bytes))
      rw [remainderBytes_append_short _ _ small',counts.2]
      simpa only [tailSize] using tailT
    · rw [counts.2]
      change t.external[stackPtr initial-89]? = some (UInt8.ofNat _)
      rw [lengthT]
      change some (UInt8.ofNat ((Operand.reg 3 : Operand 8).read d).toNat) = _
      rw [lengthD,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    · rw [counts.1]
      exact countT
  refine ⟨t,?_,ripT.trans (by cases v <;> rfl),?_,?_⟩
  · rw [prefixMessage_succ inputs index input.remaining]
    exact result
  · exact (frameT.read (n:=64) (r:=14) (by simp)).trans
      ((frameD.read (n:=64) (r:=14) (by simp)).trans ((copy.abi.1 .r14 (by simp)).trans
      ((frameB.read (n:=64) (r:=14) (by simp)).trans input.indexRegister)))
  · exact (frameT.read (n:=64) (r:=15) (by simp)).trans
      ((frameD.read (n:=64) (r:=15) (by simp)).trans ((copy.abi.1 .r15 (by simp)).trans
      ((frameB.read (n:=64) (r:=15) (by simp)).trans input.countRegister)))

end Sha2.Proofs.Wrapper.Absorb
