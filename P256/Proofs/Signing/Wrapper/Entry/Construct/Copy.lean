import P256.Proofs.Signing.Wrapper.Entry.Construct.Memory
import P256.Proofs.Signing.Wrapper.Entry.Construct.ScalarCopy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program.ScalarFrame SecretKeyFromBytes.Scalar

 theorem copy_pre [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    {ip : BitVec 64} {src dst : Nat} (rip : s.RIP=ip)
    (source : src+32≤520) (destination : dst+32≤472)
    (apart : OffsetsApart (BitVec.ofNat 64 dst) 32 (BitVec.ofNat 64 src) 32) :
    Copy32.Pre ip (fun q => stackPtr q+BitVec.ofNat 64 src)
      (fun q => stackPtr q+BitVec.ofNat 64 dst) s := by
  refine ⟨rip,?_,?_,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
      readable ctx state (off := src+_) (len := 8) (by omega)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
      writable ctx state (off := dst+_) (len := 8) (by omega) (by decide)
  · intro i hi j hj eq
    exact apart.ne (stackPtr s) hi hj (by decide) eq
  · intro i hi co cl bound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
      code_apart ctx state (off := dst+_) (len := 8) (by omega) bound

theorem copy [Bindings] {initial s : RamState} {secret message : ByteArray} {d : Nat}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x102650) (scalar : Nat256At s (stackPtr s+0) d) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      t.RIP=0x102677 ∧ Nat256At t (stackPtr t+64) d ∧
      AgreesExcept (Copy32.components (stackPtr s+64)) s t ∧
      (∀ off : Nat, 312 ≤ off → off+8 ≤ 336 →
        memLoad t.external (stackPtr s+BitVec.ofNat 64 off) 64 =
          memLoad s.external (stackPtr s+BitVec.ofNat 64 off) 64) := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  have block := ScalarCopy.run (returnBoundary initial) outside 0x2650 (by decide)
  have hp := copy_pre ctx state (src := 0) (dst := 64)
    (ip := 0x102650) rip (by decide) (by decide)
    (by unfold OffsetsApart; decide +kernel)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := block s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x2650 ScalarCopy.bytes
      (by decide) (by decide +kernel)) hp
  have ag := Copy32.frame effect
  have st := after ctx state run ready ag (by
    intro c hc a ha
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨workRegion initial,by simp,work ctx state (by decide) ha⟩)
    (by simp [Copy32.components]) (by simp [Copy32.components])
  have sp : stackPtr t=stackPtr s := ag.read (n := 64) (r := 4) (by simp [Copy32.components])
  have copied := Copy32.copy_bytes effect (readable ctx state (by decide))
    (by change MemReadable t (stackPtr s+64) 32; rw [← sp]; exact readable ctx st (by decide))
  refine ⟨fuel,t,run,st,effect.rip,?_,ag,?_⟩
  · rw [sp]
    exact ⟨scalar.1,fun i hi => (copied i hi).trans (scalar.2 i hi)⟩
  · intro off low high
    apply memLoad_agrees_apart ag
    intro addr len member
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false,false_or,
      Component.mem.injEq,reduceCtorEq] at member
    obtain ⟨rfl,rfl⟩ := member
    intro i hi j hj eq
    exact (show OffsetsApart 64 32 (BitVec.ofNat 64 off) 8 by
      simp only [OffsetsApart,BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.reduceToNat]
      omega).ne (stackPtr s) hi hj (by decide) eq

end P256.Proofs.Signing.Wrapper.Entry.Construct
