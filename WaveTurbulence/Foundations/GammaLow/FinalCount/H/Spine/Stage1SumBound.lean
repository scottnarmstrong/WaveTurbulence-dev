/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1SumBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1PieceBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.Stage1SumBound`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 TARGET L2236-L2255 (terms (a),(b) before the weights): the sum of the Stage 1 pieces with the class
count. `Stage1Data` is the data S2a delivers for one instance of the garden sum. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

structure Stage1Data (P : WTParams) (R : ℕ) where
  Pc : Type
  fin : Fintype Pc
  piece : Pc → Stage1Piece P R
  val : Pc → ℂ

/-- `bar-g` and `bar-rho` of a piece (TARGET L2237): `g_sk + g_sb`, `rho_sb + q_sk`. -/
@[expose] noncomputable def Stage1PieceD.gbar {d R : ℕ} (π : Stage1PieceD d R) : ℕ :=
  π.gsk + π.gsb

@[expose] noncomputable def Stage1PieceD.rbar {d R : ℕ} (π : Stage1PieceD d R) : ℕ :=
  π.Gsb.molecule.rho + π.Cs.hinges.card

/-- TARGET L2236-L2255 for the integral conjunct of `Represents` alone (R23 (2)); the centre loss `C_1^{n_sb}`
of R24 D3 is absorbed as `C_1^{n_sb + 2R} <= C_1^{5n}` (using `R <= 2n`, from the bond count of a sound piece) into the per-node factor `C_1^6 delta^{10 nu}`. -/
theorem stage1_sum_bound_int (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Stage1Data P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) [Fintype Cl] (cls : S.Pc → Cl) (s : ℝ) (hs0 : 0 < s)
    (hsound : ∀ π, (S.piece π).Sound p base roots)
    (hnsb : ∀ π, (S.piece π).Gsb.order ≤ n)
    (hrep : ∀ π, (S.piece π).RepresentsInt n tt base roots s (S.val π))
    (hrb : ∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ n)
    (hgb : ∀ π, (S.piece π).gbar ≤ n)
    (hpc : ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ n * (C₀ : ℝ) ^ n * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r))
    (hT2 : P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2)
    (hS2 : (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2) :
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s *
      (4 * (P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)))) := by
  letI := S.fin
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hpiece : ∀ π, ‖S.val π / (s : ℂ)‖ ≤ P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
      (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    intro π
    have h := stage1_piece_bound_int P hs hcoarse hfourier hcount hp hR hRmax (S.piece π) tt base roots
      (hsound π) (hnsb π) (S.val π) s hs0 (hrep π)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le, div_le_iff₀ hs0, mul_comm]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hs0.le)
    have hRn : R ≤ 2 * n := by
      have h1 := (hsound π).bond_count
      have h2 := hnsb π
      omega
    have hCn : P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) ≤ P.C₁ ^ (5 * n) :=
      pow_le_pow_right₀ hs.c1_ge (by have := hnsb π; omega)
    have hδp : (0 : ℝ) ≤ P.δ ^ (10 * P.ν) := Real.rpow_nonneg hs.delta_pos.le _
    have hC2 : (0 : ℝ) ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
    have hcore : (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) ≤
        (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n := by
      calc (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R)
          ≤ (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (5 * n) :=
            mul_le_mul_of_nonneg_left hCn (by have := hs.c1_ge; positivity)
        _ = (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n := by rw [mul_pow, mul_pow, ← pow_mul]; ring
    have hL1 : 0 ≤ P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) :=
      Real.rpow_nonneg hL0.le _
    have hL2 : 0 ≤ P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
        (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) := Real.rpow_nonneg hL0.le _
    have hL3 : 0 ≤ P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := Real.rpow_nonneg hL0.le _
    have hrw : P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) =
        P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
      rw [← Real.rpow_mul_natCast hL0.le, ← Real.rpow_mul_natCast hL0.le]
      simp only [Stage1PieceD.gbar, Stage1PieceD.rbar, Nat.cast_add]
      ring_nf
    rw [hrw]
    calc P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) *
        (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))
        = P.C₂ * ((P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R)) *
        (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by ring
      _ ≤ _ := by
        gcongr
  have hdelta : (0 : ℝ) ≤ P.C₁ ^ 6 * P.δ ^ (10 * P.ν) :=
    mul_nonneg (by have := hs.c1_ge; positivity) (Real.rpow_nonneg hs.delta_pos.le _)
  have := class_sum_bound (fun π => S.val π / (s : ℂ)) (fun π => (S.piece π).gbar) (fun π => (S.piece π).rbar) n R (6 * C₀)
    P.C₂ (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) (P.L ^ (-(P.ν * P.η))) (P.L ^ (-P.η ^ 6 / 4))
    (P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) P.C₂
    (by linarith [hs.c1_ge, hs.c1_le_c2]) hdelta (Real.rpow_nonneg hL0.le _)
    (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
    (by linarith [hs.c1_ge, hs.c1_le_c2]) hpiece hrb hgb
    (piece_count_of_direct_count (fun π => (S.piece π).gbar) (fun π => (S.piece π).rbar) n R C₀ P.C₂
      (by linarith [hs.c1_ge, hs.c1_le_c2]) (by convert hpc)) hT2 hS2
  have hsum : ∑ π, S.val π / (s : ℂ) = (∑ π, S.val π) / (s : ℂ) := by rw [Finset.sum_div]
  rw [hsum, norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le, div_le_iff₀ hs0] at this
  rw [mul_comm]
  convert this using 2

/-- TARGET L2236-L2255: `stage1_sum_bound_int` for the full `Represents`. -/
theorem stage1_sum_bound (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Stage1Data P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (tt : Fin (2 * R) → ℝ) (Cl : Type) [Fintype Cl] (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (hs0 : 0 < s)
    (hsound : ∀ π, (S.piece π).Sound p base roots)
    (hnsb : ∀ π, (S.piece π).Gsb.order ≤ n)
    (hrep : ∀ π, (S.piece π).Represents n tt base roots (members (cls π)) (sel π) F s (S.val π))
    (hrb : ∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ n)
    (hgb : ∀ π, (S.piece π).gbar ≤ n)
    (hpc : ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ n * (C₀ : ℝ) ^ n * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r))
    (hT2 : P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2)
    (hS2 : (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2) :
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s *
      (4 * (P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)))) :=
  stage1_sum_bound_int P hs hcoarse hfourier hcount hp hR hRmax S tt base roots C₀ Cl cls s hs0
    hsound hnsb (fun π => (hrep π).2) hrb hgb hpc hT2 hS2
