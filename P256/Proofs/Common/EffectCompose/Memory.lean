import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Instructions.LegacyLoad
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Common.Instructions.CrossPageStore (Pre Writable movM32Imm32LegacyEffect movM32R32LegacyEffect)
open X86Proofs

namespace P256.Proofs.Common.EffectCompose.CrossPageStore

variable {e : Effect} {s t : RamState}

theorem _root_.P256.Proofs.Common.Instructions.CrossPageStore.Writable.of_holds {a : BitVec 64} {len : Nat} (h : e.Holds s t)
    (hw : Writable s a len) : Writable t a len :=
  ⟨hw.toMemReadable.of_holds h, hw.tables⟩

theorem _root_.P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds {p nxt : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    (h : e.Holds s t) (ho : Obs (e.after s true) t) (hrip : e.rip = p)
    (hw : Writable s (am.addr (e.after s true) nxt) len)
    (hap : RangeApart (am.addr (e.after s true) nxt) len p codeLen) :
    Pre p codeLen (fun u => am.addr u nxt) len t :=
  ⟨h.rip_of hrip, by rw [← AddrMode.addr_obs ho]; exact hw.of_holds h,
    by rw [← AddrMode.addr_obs ho]; exact hap⟩

@[x86_local] theorem movM32R32LegacyEffect_local (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    Effect.Local (movM32R32LegacyEffect p src am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM32R32LegacyEffect, storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [movM32R32LegacyEffect, storeEffect, Write.Full, Operand.Full]

@[x86_local] theorem movM32Imm32LegacyEffect_local (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) :
    Effect.Local (movM32Imm32LegacyEffect p am imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM32Imm32LegacyEffect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM32Imm32LegacyEffect, storeEffect, Write.Full, Operand.Full]

attribute [x86_compose] movM32R32LegacyEffect movM32Imm32LegacyEffect

end P256.Proofs.Common.EffectCompose.CrossPageStore

namespace P256.Proofs.Common.Instructions.LegacyLoad

@[x86_local] theorem movR32M32LegacyEffect_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (movR32M32LegacyEffect p dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movR32M32LegacyEffect, AddrMode.addr_obs h, h.read_mem]
  · intro s
    simp [movR32M32LegacyEffect, Write.Full, Operand.Full]

attribute [x86_compose] movR32M32LegacyEffect

end P256.Proofs.Common.Instructions.LegacyLoad

namespace P256.Proofs.Common.EffectCompose
open X86 X86.Machine X86.UserProcess

@[x86_compose] theorem memLoad_memStore_narrow (m : Ram) (a : BitVec 64)
    {n k : Nat} (v : BitVec n) (hk : k % 8 = 0) (hkn : k ≤ n) (hn : n ≤ 128) :
    memLoad (memStore m a v) a k = v.setWidth k := by
  apply Bytes.memLoad (hn := hk) (h128 := by omega)
  intro i hi
  have hs := Bytes.store_self m a v hn i (by omega)
  rw [hs]
  congr 1
  simp only [storedByte_eq_extract, BitVec.extractLsb'_setWidth_of_le (show 8 * i + 8 ≤ k by omega)]

@[x86_local] theorem movzxR32M8Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) : Effect.Local (movzxR32M8Effect p len dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movzxR32M8Effect, AddrMode.addr_obs h, h.read_mem]
  · intro s
    simp [movzxR32M8Effect, Write.Full, Operand.Full]

attribute [x86_compose] movzxR32M8Effect

end P256.Proofs.Common.EffectCompose
