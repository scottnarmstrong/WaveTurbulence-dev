/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Rows
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint

/-! # P2: `SumintPar.Admissible` for the piece datum (4d-A item (d); engine datum, item 3)

`SumintPar.SumintDatum.Admissible` splits into a *structural* part (the affine algebra (ii), (iii), `Λ ≥ 1`, `∏ Λ ≤ A^M`,
unit coefficients, unit intervals `≤ 𝔇`, `d+1 ≤ wN`, `d < wDec`), the *weight bounds*, and the *bad-case clause*
(a)/(c)/(d).  Neither the structural part nor the bad-case clause mentions the weights.

* `StructAdm D`: the conjuncts of `Admissible` about the affine structure of `D` only.
* `BadClauseP D`: the bad-case clause (a)/(c)/(d) (clause (b) is carried by the `r`-dependence of `wK` and the prefactor
  `|r|`, kind `1` imposes no clause);  `badAt_kind0/2/3`: it holds at a block of the respective kind.
* **`hAdm_of_struct`**: the engine hypothesis `hAdm` (every weight family with the `WeightBounds` of `D` gives an
  `Admissible` datum) from `StructAdm D` and `BadClauseP D`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A

variable {d : ℕ}

/-- The rows `T₁, T₂, 0` of the `(iii)` clause (a function of the two matrices, so that it is unaffected by record updates). -/
def rowTf {V : Type} (T₁ T₂ : V → V → ℤ) : V ⊕ V ⊕ Fin 4 → V → ℤ := fun z => match z with
  | .inl w => T₁ w | .inr (.inl w) => T₂ w | .inr (.inr _) => 0

/-- The rows `H₁, H₂, e_c` of the `(iii)` clause. -/
def rowHf {V : Type} (H₁ H₂ : V → Fin 4 → ℤ) : V ⊕ V ⊕ Fin 4 → Fin 4 → ℤ := fun z => match z with
  | .inl w => H₁ w | .inr (.inl w) => H₂ w | .inr (.inr c) => Pi.single c 1

/-- The structural part of admissibility (about the affine structure and the unit intervals of `D` only): the conjuncts of
`SumintPar.SumintDatum.Admissible` other than the weight bounds and the bad-case clause. -/
def StructAdm (D : SumintPar.SumintDatum d) (A _L _γ _η : ℝ) (Dsteps : ℕ) : Prop :=
  (∀ v, (∀ v', IsUnitCoeff (D.σk v v')) ∧ (∀ c, IsUnitCoeff (D.σe v c)) ∧
    ((Finset.univ.filter fun v' => D.σk v v' ≠ 0).card +
      (Finset.univ.filter fun c => D.σe v c ≠ 0).card ≤ D.Λ v) ∧
    (∀ w, D.prev v = some w → D.S.LexLt w v) ∧
    (∀ v'', D.T₂ v v'' - (D.prev v).elim 0 (fun w => D.T₂ w v'') =
      ∑ v', D.σk v v' * D.T₁ v' v'') ∧
    ∀ c, D.H₂ v c - (D.prev v).elim 0 (fun w => D.H₂ w c) =
      ∑ v', D.σk v v' * D.H₁ v' c + D.σe v c) ∧
  (∀ v, 1 ≤ D.Λ v) ∧ ((∏ v, (D.Λ v : ℝ)) ≤ A ^ D.S.M) ∧
  (∀ v, ∃ a b : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4,
    (∀ v', rowTf D.T₁ D.T₂ a v' - rowTf D.T₁ D.T₂ b v' = if v' = v then 1 else 0) ∧
      ∀ c, rowHf D.H₁ D.H₂ a c - rowHf D.H₁ D.H₂ b c = 0) ∧
  (∀ i j c, IsUnitCoeff (D.ζc i j c)) ∧ (∀ i c, IsUnitCoeff (D.ξc i c)) ∧
  (∀ v, D.q v + 1 ≤ Dsteps) ∧ (∀ c, D.qOut c + 1 ≤ Dsteps) ∧
  (d + 1 ≤ D.wN ∧ d < D.wDec)

/-- The bad-case clause of `Admissible` (cases (a), (c)-nonvacuity and (d)). -/
def BadClauseP (D : SumintPar.SumintDatum d) : Prop :=
  ∀ i, D.S.nor i = false →
    (D.badKind i = 0 → ∃ h : 0 < D.S.m i,
      let t0 : D.S.TVar := .inl ⟨i, 0⟩
      let t1 : D.S.TVar := .inl ⟨i, ⟨1, by omega⟩⟩
      let s1 : D.S.TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
      ((s1, t0) ∈ D.constraints ∧ (t0, t1) ∈ D.constraints) ∨
        ((t1, t0) ∈ D.constraints ∧ (t0, s1) ∈ D.constraints)) ∧
    (D.badKind i = 2 → 0 < D.S.m i) ∧
    (D.badKind i = 3 → ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩))

/-- Admissibility with the weights, `g` and the bad-case clause supplied separately. -/
theorem admissible_of_struct {D : SumintPar.SumintDatum d} {A L γ η : ℝ} {Dsteps : ℕ}
    (hS : StructAdm D A L γ η Dsteps) (hbad : BadClauseP D)
    (hw : ∀ v, (∀ r, SNorm D.wN D.wDec (D.wK v r) ≤ ENNReal.ofReal (L ^ (-weightExp d γ η * D.g v))) ∧
      SNorm D.wN 0 (D.wL v) ≤ ENNReal.ofReal (L ^ (-weightExp d γ η * D.g' v))) :
    D.Admissible A L γ η Dsteps := by
  obtain ⟨h1, h2, h3, h4, h6a, h6b, h7, h8, h10⟩ := hS
  refine ⟨h1, h2, h3, fun v => ?_, hw, h6a, h6b, h7, h8, hbad, h10⟩
  obtain ⟨a, b, h⟩ := h4 v
  refine ⟨a, b, fun v' => ?_, fun c => ?_⟩
  · rcases a with a | a | a <;> rcases b with b | b | b <;> exact h.1 v'
  · rcases a with a | a | a <;> rcases b with b | b | b <;> exact h.2 c

theorem structAdm_update {D : SumintPar.SumintDatum d} {A L γ η : ℝ} {Dsteps : ℕ}
    (hS : StructAdm D A L γ η Dsteps) (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom d → Mom d → ℂ)
    (b : D.S.VIdx → Mom d → ℂ) :
    StructAdm ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum d) A L γ η Dsteps := by
  obtain ⟨h1, h2, h3, h4, h6a, h6b, h7, h8, h10⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h6a
  · exact h6b
  · exact h7
  · exact h8
  · exact h10

/-- **`hAdm` of the engine** from the structural part and the bad-case clause of the datum. -/
theorem hAdm_of_struct {D : SumintPar.SumintDatum d} {A L γ η : ℝ} {Dsteps : ℕ}
    (hS : StructAdm D A L γ η Dsteps) (hbad : BadClauseP D) :
    ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom d → Mom d → ℂ) (b : D.S.VIdx → Mom d → ℂ),
      WeightBounds D L γ η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum d).Admissible A L γ η Dsteps := by
  intro p a b hwb
  refine admissible_of_struct (D := { D with param := p, wK := a, wL := b }) ?_ hbad hwb
  exact structAdm_update hS p a b

end WaveTurbulence.VineEstS5C.P2
