import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Prefix
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreReach
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Result
import AesGcm.Proofs.Machine.Runtime.Root.Encrypt
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem execute [bindings : Machine.Bindings] {initial : RamState}
    {key : Vector UInt8 16} {nonce : Vector UInt8 12} {aad bytes : ByteArray} {capacity : Nat}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall initial key nonce aad bytes capacity) :
    let fit := (initial.regValue .r9).toNat + 16 ≤ capacity
    let size := if fit then bytes.size + 16 else bytes.size
    ∃ fuel final ret ciphertext tag,
      UniqueExecution initial fuel final ∧ SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧ CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧ GCM.ciphertextAndTag .aes128 key nonce aad bytes = some (ciphertext, tag) ∧
      final.regValue .rax = (if fit then 0 else 1) ∧
      RamWriteFrame initial.external final.external
        [(entryActivation initial ret).region, InPlace.outputRegion initial size] ∧
      (InPlace.outputRegion initial size).HasBytes final.external
        (if fit then ciphertext ++ ⟨tag.toArray⟩ else ciphertext) := by
  obtain ⟨ret, hframe, args, mem, initRun, hinit⟩ := reaches_core hCall
  obtain ⟨args', mem', ciphertext, tag, core, hmodel, hcore⟩ := core_reaches hCall args mem hinit
  obtain ⟨out, tailRun, tagEq, doneAtoms, statusEq, frame, dataEq⟩ :=
    exec_of_corePost hCall args' mem' hcore
  have hloaded : ProgramLoaded initial := hCall.elim (fun h => h.programLoaded) (fun h => h.2.programLoaded)
  have hpc : initial.RIP = aes128gcmEncryptInPlace.entryAddress :=
    hCall.elim (fun h => h.entry) (fun h => h.2.entry)
  have rel : Rel Extracted.programImage LIR.lifted
      ⟨LIR.lifted.locationOf .l101380 initial, []⟩ initial :=
    root_lifted_entry hm hb hloaded (fun _ h => h) hpc
  have near := nearReturn64Boundary_eq initial rel.ready.dataReady hm.integer.ss hframe.memReadable
  have sim := root_simulation hb (boundary := returnBoundary initial) (by
    intro hp
    exact hframe.retOutside _ hp.choose_spec (by exact hframe.returnBoundary.1))
  have exec := Program.Exec.of_sem ((initRun.trans core).exec tailRun.sem)
  have sp : out.values[4] = ⟨64, (returnBoundary initial).rsp⟩ := by
    rw [hframe.returnBoundary.2]
    exact doneAtoms.1
  obtain ⟨fuel, final, hu, hm', hb', hsaved, hdf, hr, rax⟩ :=
    root_execution_of_frame hframe hb near sim rel exec (hframe.returnBoundary.1 ▸ tagEq)
      sp doneAtoms rfl (by decide) (by decide) (by decide) (by decide)
  rw [hr.store] at frame dataEq
  exact ⟨fuel, final, ret, ciphertext, tag, hu, hm', hb', hsaved, hdf, hmodel,
    Value.eq_bits (rax.symm.trans statusEq), frame, dataEq⟩

theorem stack_contains {initial : RamState} {ret : BitVec 64} {x : Nat}
    (hx : (entryActivation initial ret).region.Contains x) :
    (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16).Contains x := by
  have h := Activation.ofEntry_region_within x hx
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at h ⊢
  omega

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
