import P256.Proofs.Generate.Wrapper.Tail.Sampler
import P256.Proofs.Generate.Wrapper.Tail.EncodeArgs
import P256.Proofs.Generate.Wrapper.Tail.Call
import P256.Proofs.Generate.Wrapper.Tail.Capacity
import P256.Proofs.Generate.Wrapper.Tail.ScalarCopy
import P256.Proofs.Generate.Wrapper.Tail.SerializeArgs
import P256.Proofs.Generate.Wrapper.Tail.SerializeCall

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem compute [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat} (sampler : Sampler.Contract bindings)
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106df9 ∧
      Bytes t.external (initial.regValue .rcx+8) 32
        (fun i => UInt8.ofNat (d / 256^(31-i) % 256)) ∧
      (MemoryRegion.mk (stackPtr initial-256).toNat 65).HasBytes t.external
        (Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G)) := by
  have outside := outer_boundary call hm hb
  obtain ⟨a,sa,ipa,buf,scalar,affine⟩ := sample_correct sampler hb hm call draw
  obtain ⟨b,sb,ipb,dstb,srcb,_,memb⟩ := encode_arguments sa outside ipa buf
  have scalarB : SecretKeyFromBytes.Scalar.Nat256At b (stackPtr initial-184) d := by
    exact ⟨scalar.1,fun i hi => by rw [memb]; exact scalar.2 i hi⟩
  have affineB := affine.of_bytes_eq (fun i hi => by rw [memb])
  obtain ⟨c,sc,ipc,encoded,affineC⟩ := encode_call call sb outside ipb srcb dstb scalarB affineB
  obtain ⟨e,_,se,ipe,age⟩ := capacity_payload call draw outside sc ipc
  have me := age.external (by simp [Component.Covers])
  obtain ⟨f,sf,ipf,scalarF,agf⟩ := scalar_copy call draw se outside ipe (by rwa [me])
  have affineF : Sec1.AffineAt f (stackPtr initial-152) (Points.mul d Operations.domain.G) := by
    apply affineC.of_bytes_eq
    intro i hi
    rw [agf.byte ?_,me]
    intro comp hc cover
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact cover.elim
    obtain ⟨j,hj,eq⟩ := cover
    exact output_apart_stack call draw (off := 152) (len := 65)
      (outOff := 8) (outLen := 32) (by decide) (by decide) (by decide) j hj i hi eq.symm
  obtain ⟨g,sg,ipg,srcg,dstg,rdxg,affineG,memg⟩ := prepare_serializer sf outside ipf affineF
  obtain ⟨t,st,ipt,point,frame⟩ := serialize_call call sg outside ipg srcg dstg rdxg affineG
  refine ⟨t,st,ipt,?_,point⟩
  intro i hi
  rw [frame _ ?_,memg]
  · exact scalarF i hi
  · intro region member contained
    have eq : region = workRegion initial := by simpa using member
    subst region
    exact output_stack_disjoint call _
      (output_contains call draw (off := 8) (len := 32) (by decide) ⟨i,hi,rfl⟩)
      (work_in_stack call.stackAvailable.1 contained)

end P256.Proofs.Generate.Wrapper
