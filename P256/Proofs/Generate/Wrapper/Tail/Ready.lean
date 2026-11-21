import P256.Proofs.Generate.Wrapper.Tail.Tag
import P256.Proofs.Generate.Wrapper.Tail.Length
import P256.Proofs.Generate.Wrapper.Tail.CopyArgs
import P256.Proofs.Generate.Wrapper.Tail.Payload

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem copy_ready [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (state : OutputState initial s input) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106df9)
    (encoded : (MemoryRegion.mk (stackPtr initial-256).toNat 65).HasBytes s.external
      (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G))) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106e76 ∧
      t.regValue .rdi = initial.regValue .rcx+40 ∧ t.regValue .rsi = stackPtr initial-256 ∧
      t.regValue .rdx = 65 ∧ t.regValue .r15 = 65 ∧ t.external = s.external := by
  have tag := point_tag draw
  have size : (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G)).size = 65 := encoded.1
  rw [Array.getElem?_eq_getElem (by change 0 < (Sec1Serialize.encodedPoint _).size; rw [size]; decide)] at tag
  have byte : s.external[stackPtr initial-256]? = some 4 := by
    have h := encoded.2 ⟨0,by rw [size]; decide⟩
    change s.external[BitVec.ofNat 64 ((stackPtr initial-256).toNat+0)]? = _ at h
    simp only [Nat.add_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] at h
    exact h.trans tag
  have word : memLoad s.external (stackPtr initial-256) 8 = 4 := by
    apply Bytes.memLoad (n := 8) _ (by decide) (by decide)
    intro i hi
    have eq : i = 0 := by omega
    subst i
    change s.external[stackPtr initial-256+0]? = some 4
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using byte
  obtain ⟨a,sa,ipa,cxa,ma⟩ := tag_branch call state outside rip word
  obtain ⟨b,runB,readyB,ipb,lenB,agB⟩ := Tail.lookup_length
    (readyToStep sa.machine sa.bindingsSupported) sa.loaded outside ipa cxa
  have sb := sa.after_registers runB readyB agB (by simp [Component.Covers]) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp)
  have capB : 105 ≤ (b.regValue .rbx).toNat := by
    rw [sb.capacity]
    exact output_capacity call draw
  obtain ⟨t,runT,readyT,ipt,dst,src,cnt,agT⟩ := Tail.prepare_copy readyB sb.loaded outside ipb lenB capB
  have st := sb.after_registers runT readyT agT (by simp [Component.Covers]) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp)
  refine ⟨t,st,ipt,?_,?_,cnt,(agT.read (n := 64) (r := 15) (by simp)).trans lenB,
    ((agB.trans agT).external (by simp [Component.Covers])).trans ma⟩
  · exact dst.trans (congrArg (fun v : BitVec 64 => v+40) sb.output)
  · rw [src,sb.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]

end P256.Proofs.Generate.Wrapper
