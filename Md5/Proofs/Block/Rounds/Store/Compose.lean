import Md5.Proofs.Memory.Basic
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Md5.Proofs.Memory

open X86 X86.Machine X86.UserProcess X86Proofs

variable {e : Effect} {s s' : RamState}

theorem MemWritable.of_holds {a : BitVec 64} {len : Nat} (h : e.Holds s s')
    (hm : MemWritable s a len) : MemWritable s' a len :=
  ⟨hm.low, fun i hi ↦ h.agrees.grow _ (hm.bytes i hi), hm.tables⟩

theorem StorePre.of_holds {p nxt : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    (h : e.Holds s s') (ho : Obs (e.after s true) s') (hrip : e.rip = p)
    (hw : MemWritable s (am.addr (e.after s true) nxt) len)
    (hap : RangeApart (am.addr (e.after s true) nxt) len p codeLen) :
    StorePre p codeLen (fun t ↦ am.addr t nxt) len s' :=
  ⟨h.rip_of hrip, by rw [← AddrMode.addr_obs ho]; exact hw.of_holds h,
    by rw [← AddrMode.addr_obs ho]; exact hap⟩

end Md5.Proofs.Memory

namespace Md5.Proofs.Block.Rounds.Store

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_compose] def movM32R32NoRexEffect (p : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
    fun s ↦ (Operand.reg src : Operand 32).read s

@[x86_local] theorem movM32R32NoRexEffect_local {p : BitVec 64} {src : BitVec 5}
    {am : AddrMode} : Effect.Local (movM32R32NoRexEffect p src am) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [movM32R32NoRexEffect, storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · rfl
  · cases i <;> simp_all [movM32R32NoRexEffect, storeEffect, Effect.flag]
  · simp [movM32R32NoRexEffect, storeEffect, Write.Full, Operand.Full]

end Md5.Proofs.Block.Rounds.Store
