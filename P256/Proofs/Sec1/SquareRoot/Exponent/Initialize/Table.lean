import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.FirstState
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.FirstSetup
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LastSetup
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableRound
import P256.Proofs.Sec1.SquareRoot.Exponent.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_table [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ u fuel, Advances boundary fuel s u ∧ TableState s u x 16 ∧
      u.RIP=0x1153b9 ∧ exponentWordAt u (exponentFrameBase s+0x2c8) 1 := by
  obtain ⟨t,a0,h0,ip0,ax⟩ := initialize_table_first ctx
  obtain ⟨t1,a1,h1,ip1,si1,dx1,di1,cx1,r81⟩ := first_setup ctx h0 ip0 ax
  obtain ⟨t2,f2,a2,h2,ip2,value2,_⟩ := table_multiply_call ctx h1 (by decide)
    0x14f8f 0xfffff64c (by decide) (by decide +kernel) (by decide +kernel)
    ip1 si1 dx1 di1 cx1 r81
  obtain ⟨t3,a3,h3,ip3,_⟩ := copy_table_entry ctx h2 (by decide) value2
    0x14f94 (by decide) (by decide +kernel) ip2
  obtain ⟨t4,f4,a4,h4,ip4⟩ := table_round ctx h3 (by decide)
    0x14fc8 0xfffff5ff (by decide) (by decide +kernel) ip3
  obtain ⟨t5,f5,a5,h5,ip5⟩ := table_round ctx h4 (by decide)
    0x15015 0xfffff5b2 (by decide) (by decide +kernel) ip4
  obtain ⟨t6,f6,a6,h6,ip6⟩ := table_round ctx h5 (by decide)
    0x15062 0xfffff565 (by decide) (by decide +kernel) ip5
  obtain ⟨t7,f7,a7,h7,ip7⟩ := table_round ctx h6 (by decide)
    0x150af 0xfffff518 (by decide) (by decide +kernel) ip6
  obtain ⟨t8,f8,a8,h8,ip8⟩ := table_round ctx h7 (by decide)
    0x150fc 0xfffff4cb (by decide) (by decide +kernel) ip7
  obtain ⟨t9,f9,a9,h9,ip9⟩ := table_round ctx h8 (by decide)
    0x15149 0xfffff47e (by decide) (by decide +kernel) ip8
  obtain ⟨t10,f10,a10,h10,ip10⟩ := table_round ctx h9 (by decide)
    0x15196 0xfffff431 (by decide) (by decide +kernel) ip9
  obtain ⟨t11,f11,a11,h11,ip11⟩ := table_round ctx h10 (by decide)
    0x151e3 0xfffff3e4 (by decide) (by decide +kernel) ip10
  obtain ⟨t12,f12,a12,h12,ip12⟩ := table_round ctx h11 (by decide)
    0x15230 0xfffff397 (by decide) (by decide +kernel) ip11
  obtain ⟨t13,f13,a13,h13,ip13⟩ := table_round ctx h12 (by decide)
    0x1527d 0xfffff34a (by decide) (by decide +kernel) ip12
  obtain ⟨t14,f14,a14,h14,ip14⟩ := table_round ctx h13 (by decide)
    0x152ca 0xfffff2fd (by decide) (by decide +kernel) ip13
  obtain ⟨t15,f15,a15,h15,ip15⟩ := table_round ctx h14 (by decide)
    0x15317 0xfffff2b0 (by decide) (by decide +kernel) ip14
  obtain ⟨v,aset,hset,ipset,si,dx,di,cx,r8,saved⟩ := last_setup ctx h15 ip15
  obtain ⟨w,fc,ac,hc,ipc,value,bytes⟩ := table_multiply_call ctx hset (by decide)
    0x15380 0xfffff25b (by decide) (by decide +kernel) (by decide +kernel)
    ipset si dx di cx r8
  have savedW : exponentWordAt w (exponentFrameBase s+0x2c8) 1 :=
    (exponent_word_of_bytes (n := 64) (fun j hj ↦
      bytes 0x2c8 8 (by decide) (by decide) j hj)).trans saved
  obtain ⟨u,acopy,hu,ipu,g⟩ := copy_table_entry ctx hc (by decide) value
    0x15385 (by decide) (by decide +kernel) ipc
  have savedU : exponentWordAt u (exponentFrameBase s+0x2c8) 1 := by
    apply Eq.trans ?_ savedW
    apply exponent_word_of_bytes
    intro j hj
    apply g.memory
    intro c hc hv
    simp only [tableCopyComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    obtain ⟨k,hk,eq⟩ := hv
    have apart : RangeApart (exponentFrameBase s+640#64) 32
        (exponentFrameBase s+712#64) 8 :=
      RangeApart.offsets (exponentFrameBase s) (by decide) (by decide) (by decide)
    exact apart k hk j hj eq.symm
  exact ⟨u,173+5+f2+8+f4+f5+f6+f7+f8+f9+f10+f11+f12+f13+f14+f15+6+fc+8,(((((((((((((((((a0.trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans aset).trans ac).trans acopy,hu,ipu,savedU⟩

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
