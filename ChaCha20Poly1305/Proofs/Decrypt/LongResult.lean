import ChaCha20Poly1305.Proofs.Decrypt.Supply

namespace ChaCha20Poly1305.Proofs.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Wrapper Detached Standards.RFC.ChaCha20Poly1305

set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 850000
set_option maxRecDepth 8000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Packet.good memLoad memStore poly1305Mac poly1305KeyGen chacha20Encrypt

theorem longRun {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (long : 16≤msg.size) (small : msg.size<2^32)
    {ret cap : BitVec 64} (hret : (Stack.returnSlot s).Word64At s.external ret)
    (rl : ret.toNat<userAddressLimit) (outside : ¬InProgram ret)
    (hcap : StackArgument s 2 cap) (room : (heapRegion decrypt s).size≤cap.toNat) :
    let p := packet key nonce aad msg (s.regValue .rdx) (s.regValue .r8) long small
    Runs (lifted.locationOf .l1014c0 s) (Completed p (Activation.ofEntry s decrypt.minStackBytes ret) (BitVec.ofNat 64 msg.size)) := by
  let e := Short.envOf s msg cap
  let root := Activation.ofEntry s decrypt.minStackBytes ret
  let c := {root with rbp:=1,r12:=root.r8+e.n,r13:=Short.limit e,rdx:=0}
  let p := packet key nonce aad msg (s.regValue .rdx) (s.regValue .r8) long small
  have geo := Short.call_geometry_lt hc room (by omega) small
  obtain ⟨x,keyE,ctE,start⟩ := Prefix.initial hc (by omega) hret rl outside hcap room
  apply Prefix.run (e:=e) (x:=x) geo start
  intro a entry
  apply suffix root p e.n (BitVec.ofNat 64 aad.size) a
  exact supply hc long small ret cap geo x keyE ctE a entry

theorem longInput [b : Bindings] {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hb : MachineRamUnitStrideDecodable b s)
    (hm : SupportedIntegerMachineState b.processor s) (hc : ValidCall decrypt s [key,nonce,aad,msg]) (long : 16≤msg.size) :
    ∃ fuel t, UniqueExecution s fuel t ∧ SupportedIntegerMachineState b.processor t ∧
      MachineRamUnitStrideDecodable b t ∧ CalleeSavedRegistersUnchanged s t ∧ DirectionFlagUnset t ∧
      match AEAD.decryptWithTag aad key nonce msg with
      | some plaintext => SuccessfulStatus t ∧ MemoryWriteFrame s t #v[outputRegion decrypt s,heapRegion decrypt s,
          allocatorStateRegion,Stack.region s decrypt.minStackBytes] ∧ readOutput decrypt s t=.ok plaintext
      | none => FailureStatus t aeadErrorStatus ∧ MemoryWriteFrame s t #v[heapRegion decrypt s,allocatorStateRegion,
          Stack.region s decrypt.minStackBytes] := by
  have src : (s.regValue .rcx).toNat+msg.size<2^32 := hc.inputsInMemory.2.2.2.1.1
  have small : msg.size<2^32 := by omega
  obtain ⟨ret,hret,rl,outside⟩ := hc.returnAddress
  obtain ⟨cap,sc,room⟩ := hc.heapLengthArgumentCoversHeap _ rfl
  let p := packet key nonce aad msg (s.regValue .rdx) (s.regValue .r8) long small
  let fr := Activation.ofEntry s decrypt.minStackBytes ret
  let total := BitVec.ofNat 64 msg.size
  have count : total.toNat=msg.size := Nat.mod_eq_of_lt (by omega)
  have n : p.n.toNat=msg.size-16 := by
    change (BitVec.ofNat 64 (msg.size-16)).toNat=_
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have pre := callPre hc hret rl outside
  obtain ⟨o,run,r⟩ := longRun hc long small hret rl outside sc room
  change Completed p fr total o at r
  have heap : (⟨p.buf.toNat,total.toNat⟩ : MemoryRegion)=heapRegion decrypt s := by rw [Short.heap_region hc,count]; rfl
  have output : (⟨fr.r9.toNat,p.n.toNat⟩ : MemoryRegion)=outputRegion decrypt s := by rw [output_region hc,n]; rfl
  let stk := Stack.region s decrypt.minStackBytes
  let rs0 := #v[heapRegion decrypt s,allocatorStateRegion,stk]
  let rs1 := #v[outputRegion decrypt s,heapRegion decrypt s,allocatorStateRegion,stk]
  have decryptE : AEAD.decryptWithTag aad key nonce msg=if p.good then some p.plain else none := decryptPacket
  rw [decryptE]
  cases hg : p.good
  · simp only [Bool.false_eq_true,ite_false]
    obtain ⟨fuel,t,unique,hw,hd,abi,df,frame,back⟩ := machineResult hb hm hc pre run r.returned (rs:=rs0) (by
      apply outside_of_within
      change ∀ z ∈ fr.region :: resultFoot p total fr.r9, _
      simp only [resultFoot,commonFoot,hg,Bool.false_eq_true,ite_false,List.append_nil,heap,
        List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨⟨stk,by simp [rs0],Activation.ofEntry_region_within⟩,⟨_,by simp [rs0],fun _ h => h⟩,⟨_,by simp [rs0],fun _ h => h⟩⟩)
    have hv := back.regs 0 (by decide) (by decide +kernel)
    have status : o.values[0]=⟨64,1⟩ := by simpa only [hg,Bool.false_eq_true,ite_false] using r.status
    have reg : t.regValue .rax=1 := Value.eq_bits (hv.symm.trans status)
    exact ⟨fuel,t,unique,hw,hd,abi,df,by simp [FailureStatus,reg,aeadErrorStatus],frame⟩
  · simp only [ite_true]
    obtain ⟨fuel,t,unique,hw,hd,abi,df,frame,back⟩ := machineResult hb hm hc pre run r.returned (rs:=rs1) (by
      apply outside_of_within
      change ∀ z ∈ fr.region :: resultFoot p total fr.r9, _
      simp only [resultFoot,commonFoot,hg,ite_true,List.cons_append,List.nil_append,heap,output,
        List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨⟨stk,by simp [rs1],Activation.ofEntry_region_within⟩,⟨_,by simp [rs1],fun _ h => h⟩,
        ⟨_,by simp [rs1],fun _ h => h⟩,⟨_,by simp [rs1],fun _ h => h⟩⟩)
    have hv := back.regs 0 (by decide) (by decide +kernel)
    have status : o.values[0]=⟨64,0⟩ := by simpa only [hg,ite_true] using r.status
    have reg : t.regValue .rax=0 := Value.eq_bits (hv.symm.trans status)
    refine ⟨fuel,t,unique,hw,hd,abi,df,by simp [SuccessfulStatus,reg],frame,?_⟩
    have needs := (needsPacket (pa:=s.regValue .rdx) (heap:=s.regValue .r8) (h:=long) (small:=small)).trans hg
    have ok := hc.outputInMemory needs
    rw [bufferEq hc] at ok
    have size : p.plain.size=p.n.toNat := (ChaChaRound.encryptedSize p.key p.nonce 1 p.ct).trans p.length.symm
    have rd : Readable s.external fr.r9 p.plain.size := Readable.of_allocated ok.1 ok.2 (Nat.le_refl _) (by
      change fr.r9.toNat+p.plain.size≤fr.r9.toNat+(msg.size-16); rw [size,n]; exact Nat.le_refl _)
    have bytes := r.output hg
    unfold Packet.dst Stream.encode at bytes
    rw [←size,BitVec.setWidth_eq] at bytes
    have atOut := bytesFromPacked (rd.of_frame r.returned.frame) bytes
    rw [back.store] at atOut
    unfold readOutput
    rw [←output,←size]
    exact readRegion_of_bytes atOut

end ChaCha20Poly1305.Proofs.Decrypt
