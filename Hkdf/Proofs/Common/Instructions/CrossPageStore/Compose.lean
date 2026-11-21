import Hkdf.Proofs.Common.Instructions.CrossPageStore.Mov
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86Proofs

theorem storePre_of_holds {e : Effect} {s t : RamState}
    {p nxt : BitVec 64} {am : AddrMode} {len codeLen : Nat}
    (h : e.Holds s t) (ho : Obs (e.after s true) t) (hrip : e.rip = p)
    (hw : Common.Instructions.CrossPageStore.Writable s (am.addr (e.after s true) nxt) len)
    (hap : RangeApart (am.addr (e.after s true) nxt) len p codeLen) :
    Common.Instructions.CrossPageStore.Pre p codeLen (fun u => am.addr u nxt) len t :=
  ⟨h.rip_of hrip, by
    rw [← AddrMode.addr_obs ho]
    exact ⟨hw.toMemReadable.of_holds h, hw.tables⟩,
    by rw [← AddrMode.addr_obs ho]; exact hap⟩

end Hkdf.Proofs.Common.Instructions.CrossPageStore
