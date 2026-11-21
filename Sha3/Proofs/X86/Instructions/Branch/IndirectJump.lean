import X86Proofs.Instructions.Call.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_FF_jmp_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 4) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0xFF)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.JMP_MEMv (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0xFF modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcodeFF a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0OpcodeFF_run_of_jmp_memory a u _ ctx _ hmod hreg hmode hfe hf)

theorem jmp_m_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hmode64 : ctx.is_mode64 = true) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64)
    (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (h : DataReady t) (hread : MemReadable t addr 8)
    (htarget : ((Operand.mem addr : Operand 64).read t).toNat < 2^32) :
    (X86.Instructions.JMP_MEMv ip ctx mod rm).run s =
      (.ok (), jumpState (dataAccess t "load") next
        ((Operand.mem addr : Operand 64).read t)) := by
  have hcontext :
      ({ ctx with is_mode64 := true, address_size := 64, lock_prefix_present := false } :
        Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea
  rw [← hcontext]
  have hread' := logicalMemRead_run t h isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hread.low hread.mem
  have hb : BranchReady (withNextIP (dataAccess t "load") next) :=
    h.branchReady.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
  unfold X86.Instructions.JMP_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread',
    X86.Instructions.Operations.JMP_NEAR => jmp_operation_abs _ _ _ _ hb htarget]

theorem jmp_m64_rip_step [Bindings] (s : RamState) (h : ReadyToStep s) (disp : BitVec 32)
    (hcode : BytesAt s s.RIP ([0xff, 0x25] ++ immBytes 32 disp))
    (hlow : s.RIP.toNat + 6 ≤ 2^32)
    (hread : MemReadable s (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)) 8)
    (htarget : ((Operand.mem (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)) :
      Operand 64).read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s 6 fun t =>
      jumpState (dataAccess t "load") (BitVec.add s.RIP 6#64)
        ((Operand.mem (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)) :
          Operand 64).read s))) := by
  have hlow' : s.RIP.toNat + ([0xff, 0x25] ++ immBytes 32 disp).length ≤ 2^32 := by
    simpa using hlow
  have hdecode := decodeLegacy0_run_of_FF_jmp_memory s h _ 0 0x25 (by decide) (by decide)
    hcode hlow' rfl rfl (by decide) (legacyContext s.DS) rfl
  rw [show modrmMod 0x25 = (AddrMode.rip disp).mod from rfl,
    show modrmRm 0x25 = (AddrMode.rip disp).rm from rfl,
    show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at hdecode
  have hea := memAlu_ea s h [] 0xff 4 (.rip disp) trivial [] (legacyContext s.DS)
    (AddrContext.legacy _ (.rip disp) rfl rfl)
    (by simpa [AddrMode.modrm, AddrMode.mod, AddrMode.rm, AddrMode.tail] using hcode)
    (by simpa [AddrMode.tail] using hlow') (by simp [AddrMode.tail])
  have hrip := handleRIPRelativeAddress_addrMode_run (.rip disp) (beforeFetch s)
    (BitVec.add s.RIP 6#64)
  simp only [List.length_nil, Nat.zero_add, AddrMode.tail, immBytes_length,
    Nat.reduceAdd, Nat.reduceDiv] at hea
  rw [jmp_m_form _ _ _ _ _ _ rfl rfl rfl _ _ _ _ _ hea hrip (memAlu_dataReady h 7)
    (hread.of_external_eq rfl) htarget] at hdecode
  have hmode : In64BitMode
      (jumpState (dataAccess (afterFetches (beforeFetch s) 7) "load") (BitVec.add s.RIP 6#64)
        ((Operand.mem (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)) :
          Operand 64).read s)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xff (0x25 :: immBytes 32 disp)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode hmode

theorem AgreesExcept.afterStep_jmp_memory (s : RamState) (length : Nat)
    (nextIP target : BitVec 64) :
    AgreesExcept [.rip] s
      (afterStep s length fun t => jumpState (dataAccess t "load") nextIP target) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, jumpState, dataAccess, afterFetches,
      beforeFetch, resetStepFields]

theorem jmp_m64_rip_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 32) :
    StepEffect (fun s => s.RIP = p ∧ MemReadable s (p + 6 + disp.signExtend 64) 8 ∧
        ((Operand.mem (p + 6 + disp.signExtend 64) : Operand 64).read s).toNat < 2^32)
      (codeRange p ([0xff, 0x25] ++ immBytes 32 disp))
      (fun s => { rip := (Operand.mem (p + 6 + disp.signExtend 64) : Operand 64).read s }) := by
  rintro s h hcode ⟨rfl, hread, htarget⟩
  have ha := AgreesExcept.afterStep_jmp_memory s 6 (BitVec.add s.RIP 6#64)
    ((Operand.mem (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)) : Operand 64).read s)
  refine ⟨_, jmp_m64_rip_step s h disp hcode.bytesAt
    (hcode.low (by simp) (by simp)) hread htarget,
    h.of_agreesExcept ha h.memory.tables, ?_⟩
  exact ⟨by simp [afterStep, finishStep, jumpState], trivial, trivial, ha⟩

end X86Proofs
