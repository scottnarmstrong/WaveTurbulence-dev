/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IsUnitCoeff
public import WaveTurbulence.Frozen.Defs.SNorm
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt
public import WaveTurbulence.Frozen.Defs.SumintShapeM
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

/-!
# SumintDatum.Admissible

Wave B tier B1 (WaveB1-Sumint.lean), source: T L1603–L1622. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- **Hypotheses (ii), (iii) and the weight bounds** of `sumint` (T L1603–L1622), with `A` the
constant of (ii) and the bad-case conditions (a), (d). Every `Λ_v ≥ 1` ("at most `Λ` terms" with
`∏ Λ ≤ C₀^M` a genuine count): a zero factor would make `∏ Λ_v ≤ A^M` vacuous and leave the other
`Λ_v` unconstrained (stage-3 R6). -/
def Admissible (A : ℝ) (L γ η : ℝ) (Dsteps : ℕ) : Prop :=
  -- (ii) as identities of affine forms: `ℓ_v - ℓ_{prev v} = ∑ σk k + ∑ σe (e,f,g,h)`
  (∀ v, (∀ v', IsUnitCoeff (D.σk v v')) ∧ (∀ c, IsUnitCoeff (D.σe v c)) ∧
    ((Finset.univ.filter fun v' => D.σk v v' ≠ 0).card +
      (Finset.univ.filter fun c => D.σe v c ≠ 0).card ≤ D.Λ v) ∧
    (∀ w, D.prev v = some w → D.S.LexLt w v) ∧
    (∀ v'', D.T₂ v v'' - (D.prev v).elim 0 (fun w => D.T₂ w v'') =
      ∑ v', D.σk v v' * D.T₁ v' v'') ∧
    ∀ c, D.H₂ v c - (D.prev v).elim 0 (fun w => D.H₂ w c) =
      ∑ v', D.σk v v' * D.H₁ v' c + D.σe v c) ∧
  (∀ v, 1 ≤ D.Λ v) ∧ ((∏ v, (D.Λ v : ℝ)) ≤ A ^ D.S.M) ∧
  -- (iii): every input variable is the difference of two of `(k, ℓ, e, f, g, h)` (as affine forms)
  (∀ v, ∃ a b : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4,
    let rowT : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4 → D.S.VIdx → ℤ := fun z => match z with
      | .inl w => D.T₁ w | .inr (.inl w) => D.T₂ w | .inr (.inr _) => 0
    let rowH : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4 → Fin 4 → ℤ := fun z => match z with
      | .inl w => D.H₁ w | .inr (.inl w) => D.H₂ w | .inr (.inr c) => Pi.single c 1
    (∀ v', rowT a v' - rowT b v' = if v' = v then 1 else 0) ∧ ∀ c, rowH a c - rowH b c = 0) ∧
  -- the weight bounds (propertyKj)
  (∀ v, SNorm (30 * d) (30 * d) (D.wK v) ≤ ENNReal.ofReal (L ^ (-(min (2 * γ)
      (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η) * D.g v)) ∧
    SNorm (30 * d) 0 (D.wL v) ≤ ENNReal.ofReal (L ^ (-(min (2 * γ)
      (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η) * D.g' v))) ∧
  -- coefficients in `{0, ±1}`
  (∀ i j c, IsUnitCoeff (D.ζc i j c)) ∧ (∀ i c, IsUnitCoeff (D.ξc i c)) ∧
  -- unit intervals inside `[0, 𝔇]`
  (∀ v, D.q v + 1 ≤ Dsteps) ∧ (∀ c, D.qOut c + 1 ≤ Dsteps) ∧
  -- the bad cases (a) and (d)
  (∀ i, D.S.nor i = false →
    (D.badKind i = 0 → ∃ h : 0 < D.S.m i,
      let t0 : D.S.TVar := .inl ⟨i, 0⟩
      let t1 : D.S.TVar := .inl ⟨i, ⟨1, by omega⟩⟩
      let s1 : D.S.TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
      ((s1, t0) ∈ D.constraints ∧ (t0, t1) ∈ D.constraints) ∨
        ((t1, t0) ∈ D.constraints ∧ (t0, s1) ∈ D.constraints)) ∧
    (D.badKind i = 2 → 0 < D.S.m i) ∧
    (D.badKind i = 3 → ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩)))

end SumintDatum
end WaveTurbulence
