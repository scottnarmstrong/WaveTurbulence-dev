/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungResonance
import Mathlib.Tactic

/-! # Triangular integral affine parametrization of arbitrary rung sequences

Each step uses two differences of actual rung/rail labels and updates the
rail label for the next step. Both inverse identities hold over any additive
commutative group, in particular the integer lattice. An empty sequence is
allowed for type I; a one-rung sequence covers the type-II Q-block.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {E : Type*} [AddCommGroup E]

/-- The product of two labels at every rung, indexed by the actual pattern list. -/
@[expose] def RungValues (E : Type*) : List RungPattern → Type _
  | [] => PUnit
  | _::ps => (E×E) × RungValues E ps

/-- Decode the coordinates successively, carrying the actual lower rail. -/
@[expose] def decodeLadder : (ps : List RungPattern) → E → RungValues E ps → RungValues E ps
  | [],_,_ => PUnit.unit
  | p::ps,d,q => (p.decode d q.1,decodeLadder ps (p.lowerAfter d q.1) q.2)

/-- Encode actual rung labels successively, with the same reconstructed rail. -/
@[expose] def encodeLadder : (ps : List RungPattern) → E → RungValues E ps → RungValues E ps
  | [],_,_ => PUnit.unit
  | p::ps,d,q =>
      let xy := p.encode d q.1
      (xy,encodeLadder ps (p.lowerAfter d xy) q.2)

/-- Successive decoding exactly recovers every actual rung label. -/
theorem decode_encode_ladder (ps : List RungPattern) (d : E) (q : RungValues E ps) :
    decodeLadder ps d (encodeLadder ps d q)=q := by
  induction ps generalizing d with
  | nil => exact PUnit.ext _ _
  | cons p ps ih =>
    rcases q with ⟨ab,q⟩
    dsimp only [encodeLadder,decodeLadder]
    rw [p.decode_encode,ih]

/-- Encoding recovers all ladder coordinates, for arbitrary ladder length. -/
theorem encode_decode_ladder (ps : List RungPattern) (d : E) (q : RungValues E ps) :
    encodeLadder ps d (decodeLadder ps d q)=q := by
  induction ps generalizing d with
  | nil => exact PUnit.ext _ _
  | cons p ps ih =>
    rcases q with ⟨xy,q⟩
    change (p.encode d (p.decode d xy),encodeLadder ps
      (p.lowerAfter d (p.encode d (p.decode d xy))) (decodeLadder ps (p.lowerAfter d xy) q))=(xy,q)
    rw [p.encode_decode,ih]

/-- The complete explicit triangular affine bijection for a ladder. -/
@[expose] def ladderChart (ps : List RungPattern) (d : E) :
    RungValues E ps ≃ RungValues E ps where
  toFun := encodeLadder ps d
  invFun := decodeLadder ps d
  left_inv := decode_encode_ladder ps d
  right_inv := encode_decode_ladder ps d

end WaveTurbulence.Vine.Param
