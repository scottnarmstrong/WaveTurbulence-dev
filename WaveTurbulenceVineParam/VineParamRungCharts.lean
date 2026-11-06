/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # The six integral affine rung charts (TARGET vineest Step 2)

The signs record the two upper rung darts and the preceding/following
upper rail darts. Their balance is t₁+t₂+s₁−s₀=0. Each chart maps the two
actual rung labels to differences of actual bond labels, with an explicit
inverse over any additive commutative group. Thus no division or lattice
index is introduced, including the single rung of the type-II Q-block.
-/

public section
namespace WaveTurbulence.Vine.Param

/-- The six balanced orientations of a four-valent rung row. -/
inductive RungPattern
  | pp | pmForward | pmBackward | mpForward | mpBackward | mm
  deriving DecidableEq

namespace RungPattern

/-- Signs of (first rung, second rung, preceding rail, following rail). -/
@[expose] def signs : RungPattern → Fin 4 → ℤ
  | .pp => ![1,1,1,-1]
  | .pmForward => ![1,-1,1,1]
  | .pmBackward => ![1,-1,-1,-1]
  | .mpForward => ![-1,1,1,1]
  | .mpBackward => ![-1,1,-1,-1]
  | .mm => ![-1,-1,-1,1]

/-- Exhaustiveness of the six cases uses precisely two outgoing darts. -/
theorem signs_exhaustive (s : Fin 4 → ℤ)
    (hs : ∀ i,s i=1 ∨ s i= -1) (hbalance : s 0+s 1+s 3-s 2=0) :
    ∃ P : RungPattern,P.signs=s := by
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2; have h3 := hs 3
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · omega
  · refine ⟨.pp,?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · omega
  · omega
  · refine ⟨.pmForward,?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · omega
  · omega
  · refine ⟨.pmBackward,?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · refine ⟨.mpForward,?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · omega
  · omega
  · refine ⟨.mpBackward,?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · omega
  · omega
  · refine ⟨.mm,?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · omega

variable {E : Type*} [AddCommGroup E]

/-- d is the incoming lower-rail label. The forward chart gives (x,y). -/
@[expose] def encode (P : RungPattern) (d : E) (ab : E×E) : E×E :=
  match P with
  | .pp => (d-ab.2,ab.1-d)
  | .pmForward => (ab.1-ab.2,ab.1-d)
  | .pmBackward => (ab.1-ab.2,ab.2-d)
  | .mpForward => (ab.2-ab.1,ab.2-d)
  | .mpBackward => (ab.2-ab.1,ab.1-d)
  | .mm => (ab.2-d,ab.1-d)

/-- The inverse affine chart recovers the actual doubled-bond labels. -/
@[expose] def decode (P : RungPattern) (d : E) (xy : E×E) : E×E :=
  match P with
  | .pp => (d+xy.2,d-xy.1)
  | .pmForward => (d+xy.2,d+xy.2-xy.1)
  | .pmBackward => (d+xy.1+xy.2,d+xy.2)
  | .mpForward => (d+xy.2-xy.1,d+xy.2)
  | .mpBackward => (d+xy.2,d+xy.1+xy.2)
  | .mm => (d+xy.2,d+xy.1)

/-- Integral affine bijectivity, without any nonzero-gap hypothesis. -/
theorem decode_encode (P : RungPattern) (d : E) (ab : E×E) :
    P.decode d (P.encode d ab)=ab := by
  cases P <;> ext <;> simp only [encode,decode] <;> abel

/-- The inverse chart also recovers both new coordinates. -/
theorem encode_decode (P : RungPattern) (d : E) (xy : E×E) :
    P.encode d (P.decode d xy)=xy := by
  cases P <;> ext <;> simp only [encode,decode] <;> abel

/-- The explicit rung reparametrization on any additive lattice. -/
@[expose] def chart (P : RungPattern) (d : E) : (E×E) ≃ (E×E) where
  toFun := P.encode d
  invFun := P.decode d
  left_inv := P.decode_encode d
  right_inv := P.encode_decode d

end RungPattern
end WaveTurbulence.Vine.Param
