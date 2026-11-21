import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Byte
import X86Proofs
import X86Proofs.Instructions.MovStore.Decode
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_m8_r8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hw : MemWritable t addr 1)
    (hmode : In64BitMode t) (hreg : (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4) :
    (X86.Instructions.MOV_MEMb_GPR8_1 ip ctx mod reg rm).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand 8)
        (movSpec ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t)) next) := by
  have hcontext : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run _ (ht.withNextIP next) isStack addr 8 (by decide)
    ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t)
    hw.low hw.mem
  unfold X86.Instructions.MOV_MEMb_GPR8_1
  simp only [writeResult, Operand.write]
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR8_run_of_low t _ hreg _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

def movM8R8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8),
      (Operand.reg src : Operand 8).read s⟩] }

@[simp] theorem movM8R8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5)
    (s : RamState) : (movM8R8Effect p len am src s).components = [.mem (am.addr s (p + BitVec.ofNat 64 len)) 1, .rip] := by simp [movM8R8Effect, Effect.components]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
