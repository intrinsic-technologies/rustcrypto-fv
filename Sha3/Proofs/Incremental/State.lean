import Sha3.Proofs.Absorption

namespace Sha3.Proofs.Incremental

open Keccak Absorption

structure State where
  lanes : Lanes
  cursor : Nat

def initial : State := ⟨fun _ ↦ 0#64, 0⟩

def byteLanes (position : Nat) (byte : UInt8) : Lanes := fun lane ↦
  packLane fun z ↦
    if 8 * lane.val + z.val / 8 = position then
      byte.toBitVec.getLsbD (z.val % 8)
    else false

def absorbByte (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (byte : UInt8) : State :=
  let lanes := fun lane ↦ state.lanes lane ^^^ byteLanes state.cursor byte lane
  if state.cursor + 1 = rate then ⟨permute lanes, 0⟩
  else ⟨lanes, state.cursor + 1⟩

def update (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (bytes : ByteArray) : State :=
  bytes.data.foldl (absorbByte permute rate) state

def canonicalState (permute : Lanes → Lanes) (rate : Nat) (bytes : ByteArray) : State :=
  ⟨fun lane ↦ absorbBlocks permute rate bytes lane ^^^
    blockLanes bytes (bytes.size / rate * rate) rate lane, bytes.size % rate⟩

def finalize (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (suffix : UInt8 := 0x06) : Lanes :=
  permute fun lane ↦ (state.lanes lane ^^^ byteLanes state.cursor suffix lane) ^^^
    byteLanes (rate - 1) 0x80 lane

end Sha3.Proofs.Incremental
