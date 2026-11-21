import K256.Proofs.Ecdh.CallSite
import K256.Proofs.Ecdh.Multiply
import K256.Proofs.Ecdh.Scalar.Calls
import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Ecdh.Wrapper.Multiply.Call
import K256.Proofs.Ecdh.Wrapper.Multiply.Return

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

set_option maxRecDepth 8192 in
theorem multiplyPeer {s : RamState} {secret key : ByteArray} {d : Nat} {peer : Generate.Generator.Multiply.Projective}
    {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (pair : a[14] = ⟨64, localSp s + 0xc0⟩) (table : a[15] = ⟨64, localSp s + 0x1058⟩)
    (scalar : ScalarAt s m 0x138 d) (source : peer.Stored m (localSp s + 0xc0))
    (valid : peer.valid) (pos : 0 < d) (bound : d < domain.n) :
    ∃ b n, Reaches .l101a65 a m .l101afa b n ∧ Caller s b n ∧
      b[12] = ⟨64, localSp s + 0x158⟩ ∧ Generate.Generator.Affine.ProjectiveAt n
        (localSp s + 0x158) (Generate.Generator.Multiply.peerWindow d peer) := by
  let sp := localSp s
  let n := Multiply.digitMemory m sp
  let mem := memStore n (sp - 8) (0x101afa : BitVec 64)
  have win : Writable Extracted.programImage m (sp - 8) 194 :=
    (state.toMemory.window call).of_offsets (addr_sub sp 8) (addr_sub sp 3936) (by decide)
  have writes := Multiply.coreCallFrame win
  obtain ⟨room,hi,loc⟩ := Scalar.stack_geometry call
  have slot : (sp - 8).toNat = (stackPtr s).toNat - 6160 := by
    rw [localSp_sub_eight]
    exact Common.stackOffset call.stackAvailable (by decide)
  have before := state.toMemory.advance call writes (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (sp - 8).toNat ∧ (sp - 8).toNat + 194 ≤ _
    omega)
  obtain ⟨push, pushed, frame, tag, apart⟩ := callSite call before 6160 (by decide) (by decide)
    0x101a65 bytes_l101a65 144 5 (fun x hx => Common.fnCode_subset_programImage x (code_l101a65 x hx))
    (by decide +kernel) 0x101afa
  have eq : s.regValue .rsp - BitVec.ofNat 64 6160 = sp - 8 := (localSp_sub_eight s).symm
  rw [eq] at push pushed frame tag apart
  have frame' : RamWriteFrame m mem [⟨(sp - 8).toNat,194⟩] := writes.trans frame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,by dsimp; omega⟩)
  have outside (k size : Nat) (above : 186 ≤ k) (fit : k+size ≤ 6152) :
      Outside [⟨(sp-8).toNat,194⟩] (sp+BitVec.ofNat 64 k) size := by
    have addr : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
      rw [BitVec.toNat_add_of_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      change (localSp s).toNat + (BitVec.ofNat 64 k).toNat < 2^64
      simp only [BitVec.toNat_ofNat]
      omega
    change sp.toNat = _ at loc
    simp only [Outside,List.mem_singleton,forall_eq,addr]
    omega
  have source' := source.of_frame frame' (outside 192 120 (by decide) (by decide))
  have scalar' := WordsAt.of_frame scalar frame' (by decide) (outside 312 32 (by decide) (by decide))
  have count : memLoad mem sp 64 = 1 := by
    apply (frame.memLoad_eq ?_).trans (Multiply.digitCount m sp)
    exact apart 6152 8 (by decide) (by decide)
  obtain ⟨b,block,rsp,tableArg,pairCount,pairArg,outputArg,tableCount,digitsArg,r12,keep⟩ :=
    Multiply.coreCall (congrArg (Value.get 64) state.rsp) win push
  have keptWidth (i : Fin Reg.count) (same : i.val ∈ [3,5,13,14,15,22,39,50,51])
      (wide : i.val ∈ [1,2,3,5,8,9,12,13,14,15]) : b[i].width = 64 :=
    (congrArg Value.width (keep i same)).trans (state.widths i wide)
  have regs : ChildRegisters s b := by
    refine ⟨rsp.trans (congrArg (Value.mk 64) eq.symm),(keep 22 (by decide)).trans state.df,?_,?_,?_,?_⟩
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact congrArg Value.width tableArg
      · exact congrArg Value.width pairCount
      · exact keptWidth 3 (by decide) (by decide)
      · exact keptWidth 5 (by decide) (by decide)
      · exact congrArg Value.width pairArg
      · exact congrArg Value.width outputArg
      · exact congrArg Value.width tableCount
      · exact congrArg Value.width digitsArg
      · exact congrArg Value.width r12
      · exact keptWidth 13 (by decide) (by decide)
      · exact keptWidth 14 (by decide) (by decide)
      · exact keptWidth 15 (by decide) (by decide)
    · exact (congrArg Value.width (keep 39 (by decide))).trans state.mxcsr
    · exact (congrArg Value.width (keep 50 (by decide))).trans state.ftw
    · exact (congrArg Value.width (keep 51 (by decide))).trans state.fcw
  rw [pair] at pairArg
  rw [table] at tableArg
  have entry : Generate.Generator.Multiply.PeerCoreEntry (Multiply.activation s mem b) b d peer :=
    Multiply.entry call pushed regs
      (congrArg (Value.get 64) pairArg)
      (congrArg (Value.get 64) tableArg)
      (congrArg (Value.get 64) digitsArg) (congrArg (Value.get 64) outputArg)
      (congrArg (Value.get 64) pairCount) (congrArg (Value.get 64) tableCount)
      (show memLoad mem (returnSlot s) 64 = _ by rw [← localSp_sub_eight]; exact tag) count valid source' scalar'
  obtain ⟨out,exec,post⟩ := Generate.Generator.Multiply.peerCoreExecution entry pos bound
  have run := Transfer.generateExec (src := .l11c880) (dst := .l11c880) (by decide) rfl exec
  have reach := Scalar.resumeCall block run post.1
  obtain ⟨caller,saved,point⟩ := Multiply.afterCore call pushed entry
    (congrArg (Value.get 64) ((keep 3 (by decide)).trans state.output)) (congrArg (Value.get 64) r12) post
  exact ⟨_,_,reach,caller,saved,point⟩

end K256.Proofs.Ecdh.Wrapper
