import K256.Proofs.Ecdh.Wrapper.Frame
import K256.Proofs.Sec1.Tactic.Lemma.Refine
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Wrapper

structure Registers (s : RamState) (a : Values Value Reg.count) : Prop where
  rsp : a[4] = ⟨64, localSp s⟩
  args : ParseSignature.ArgumentWidths a
  savedWidths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64
  output : a[3] = ⟨64, s.regValue .rdi⟩
  peer : a[14] = ⟨64, s.regValue .rdx⟩
  r13 : a[13] = ⟨64, s.regValue .r13⟩
  df : a[22] = ⟨1, 0⟩
  mx : a[39] = (Reg.ofIndex 39).read s
  ft : a[50] = (Reg.ofIndex 50).read s
  fc : a[51] = (Reg.ofIndex 51).read s

structure Memory (s : RamState) (m : Ram) : Prop where
  frame : RamWriteFrame s.external m [Stack.region s ecdhDiffieHellman.minStackBytes]
  saved : Saved s m

theorem Memory.advance {s : RamState} {secret peer : ByteArray} {m n : Ram}
    (cur : Memory s m) (call : ValidCall ecdhDiffieHellman s [secret, peer])
    {rs : List MemoryRegion} (writes : RamWriteFrame m n rs)
    (bounds : ∀ r ∈ rs, (stackPtr s).toNat - 10088 ≤ r.start ∧
      r.start + r.size ≤ (stackPtr s).toNat - 48) : Memory s n := by
  refine ⟨cur.frame.trans writes ?_, cur.saved.of_frame call writes fun r hr => (bounds r hr).2⟩
  intro r hr
  obtain ⟨lo, hi⟩ := bounds r hr
  refine ⟨_, List.mem_singleton_self _, lo, ?_⟩
  change _ ≤ (stackPtr s).toNat - 10088 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10088))
  omega

theorem stack_geometry {s : RamState} {secret peer : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, peer]) :
    10088 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 ∧
      (localSp s).toNat = (stackPtr s).toNat - 6152 := by
  have depth : 10088 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (stackPtr s).toNat - 10088 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10088)) < 2^32 at low
  exact ⟨depth, by omega, Common.stackOffset call.stackAvailable (by decide)⟩

theorem Memory.window {s : RamState} {secret peer : ByteArray} {m : Ram}
    (cur : Memory s m) (call : ValidCall ecdhDiffieHellman s [secret, peer]) :
    Writable Extracted.programImage m (localSp s - 3936) 10088 := by
  have win := (Common.stackWritable call (off := 10088) (len := 10088)
    (by decide) (by decide) (by decide)).of_frame cur.frame
  change Writable _ m (stackPtr s - 6152 - 3936) _
  rw [show stackPtr s - 6152 - 3936 = stackPtr s - 10088 by bv_omega]
  exact win

end K256.Proofs.Ecdh.Scalar
