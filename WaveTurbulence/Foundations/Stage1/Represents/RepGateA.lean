/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.Stage1Gate
import Mathlib.Tactic

/-!
# S2 REPRESENTS: local transcription of the amended Stage 1 gate (AMEND6′+9+10, rulings R54/R55/R56)

LG-SPINE folds two amendments into AMEND6′ (announced as "AMEND6′+9+10"); until the announcement S2 states them
locally, with the exact intended text, and re-pins afterwards:
* **AMEND9 (R54, R55).** In `Stage1Piece.RepresentsInt` the bad-vine gain is `L^{-(η²/2) b_sk}` (V5's
  `VineEstCanonLayerHalf`), not `L^{-η² b_sk}`.  No later use consumes the gain (`class_piece_bound` discards it).
* **AMEND10 (R56, finding F-COUNT3).** `Stage1Counts` clauses (iii) (`≤ 6^N` pieces per class) and (iv) (class count)
  are replaced by one direct piece count `#{π | ḡ = g ∧ ρ̄ = r} ≤ 3^N C₀^N (C₀ r)! (C₀ R)! C₂^{g+r}` (TARGET L2251:
  the terms `K^eqc` are counted by gardens; LF twists replace `(T′, Q′)` so the finer classes are not `≤ 2^n`).
Everything else is textually the AMEND6′ gate of lg-spine-u (`Stage1Gate.lean`, build-fresh-a6g).
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-- AMEND9: `Stage1Piece.RepresentsInt` with the halved bad-vine gain `-(η²/2) b_sk`. -/
def Stage1Piece.RepresentsIntA {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (w : Ξ → ℂ)
    (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Integrable (fun ξ => w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots) μ ∧
    val = ∫ ξ, w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∂μ ∧
    Integrable (fun ξ => ‖w ξ‖) μ ∧
    (∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- AMEND9: `Stage1Piece.Represents` with `RepresentsIntA`. -/
def Stage1Piece.RepresentsA {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (val : ℂ) : Prop :=
  val = ∑ LG ∈ members, F.valueSel tt base roots LG (sel LG) ∧ π.RepresentsIntA n tt base roots s val

/-- AMEND10: the counts, with the direct piece count in place of clauses (iii) and (iv). -/
def Stage1CountsA (C₀ : ℕ) (P : WTParams) (R N : ℕ) (S : Stage1Data P R) (Cl : Type) (_hCl : Fintype Cl)
    (_cls : S.Pc → Cl) : Prop :=
  (∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ N) ∧ (∀ π, (S.piece π).gbar ≤ N) ∧
  ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      3 ^ N * (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)

/-- The Stage 1 reduction gate after AMEND6′+9+10 (local transcription). -/
def Stage1ReductionAtA (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∃ (S : Stage1Data P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, (S.piece π).RepresentsA N tt base roots (members (cls π)) (sel π) U.toLF s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1CountsA C₀ P R N S Cl hCl cls

/-- The η² form implies the η²/2 form (the bound only gets weaker, `L ≥ 1`). -/
theorem Stage1Piece.representsIntA_of_representsInt {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ)
    (hL : 1 ≤ P.L) (hC : 0 ≤ P.C₁) (hs : 0 ≤ s) (h : π.RepresentsInt n tt base roots s val) :
    π.RepresentsIntA n tt base roots s val := by
  exact h

/-- `Represents` implies `RepresentsA`. -/
theorem Stage1Piece.representsA_of_represents {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (val : ℂ)
    (hL : 1 ≤ P.L) (hC : 0 ≤ P.C₁) (hs : 0 ≤ s) (h : π.Represents n tt base roots members sel F s val) :
    π.RepresentsA n tt base roots members sel F s val :=
  ⟨h.1, π.representsIntA_of_representsInt n tt base roots s val hL hC hs h.2⟩

end WaveTurbulence.LGSpine
