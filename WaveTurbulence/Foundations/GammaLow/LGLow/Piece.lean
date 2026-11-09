/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.TypeGate
public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.Spine.Stage1TypeBound

/-! # LG-low (packet L07): the waist from the `𝒱_γ` gates

Main's piece/sum/core/type bounds (`Spine/Stage1{PieceBound,SumBound,CoreBound,TypeBound}.lean`), copied by source over
L5a's `𝒱_γ` pieces (`Fama.Stage1PieceG`, `Fama.Stage1DataG`, `Fama.Stage1ReductionGammaAt`), with L5c's finalsbest1
over `𝒱_γ` (`Famc.CoarseSplicedGammaAt`, premises `Famc.SplicedSourcePremisesGamma`) in place of `CoarseSplicedAt`,
and finalsbest2 over `𝒱_γ` (`Famc.FineSplicedChoicesGammaAt`, conclusions `Famc.SubproConclusionsGamma`) in place of
main's `Cover.fine_spliced_of_subpro_choices` (from `LadderFourierAt`, `FinalCountAt`). `typeGateAt_of_gamma` is the
resulting producer of `TypeGateAt`. -/

public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-- TARGET (finalproof2), L2224-L2227, for the integral conjunct of `Represents` alone (R23 (2)): the bound of
a piece value from its spliced-kernel average. The flower pieces (whose values are not `LeafFamily` values)
use this directly. The prefactor carries `C_1^{n_sb}` (R24 D3). -/
theorem stage1_piece_bound_int_gamma (P : WTParams) (hs : PieceSmall P)
    (hcoarse : Famc.CoarseSplicedGammaAt P) (hfine : Famc.FineSplicedChoicesGammaAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Fama.Stage1PieceG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : π.Sound p base roots) (hnsb : π.Gsb.order ≤ n) (val : ℂ)
    (s : ℝ) (hs0 : 0 < s) (hval : π.RepresentsInt n tt base roots s val) :
    ‖val‖ ≤ s * (P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) := by
  obtain ⟨Ξ, _, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwbound, hD⟩ := hval
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  set M : ℝ := P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) with hM
  have hKle : ∀ ξ, ‖splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ M := by
    intro ξ
    set D := π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ) with hDdef
    have hlayer : ∀ v, D.layer v ≤ p := hπ.layer_le
    have hconc : Famc.SubproConclusionsGamma P.γ π.Gsb D π.Cs P.L P.γ P.η base roots :=
      ⟨hπ.structural, rfl, fun z he hg => hπ.support z he hg, hπ.hingeOutsideFirst,
        hπ.tripleDesignated, hπ.hingeNoLoop⟩
    have hprem : Famc.SplicedSourcePremisesGamma P π.Gsb D base roots :=
      ⟨hπ.molecule, hπ.connected, hπ.atom_count, hπ.bond_count,
        ⟨π.Cs, hπ.structural, rfl, fun z he hg => hπ.support z he hg⟩⟩
    have hc := hcoarse p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos
      hπ.order_le D (hD ξ) hlayer π.ladders base roots hprem
    have hf := hfine hp hR hRmax π.Gsb
      hπ.plain hπ.irreducible hπ.balanced hπ.order_pos hπ.order_le D (hD ξ) hlayer
      hπ.molecule hπ.connected hπ.atom_count hπ.bond_count π.Cs base roots hconc
    have hν0 : 0 ≤ P.ν := hs.nu_pos.le
    have := spliced_scale_interpolation (z := splicedKernel π.Gsb D P.L P.γ P.η P.δ base roots)
      (C := P.C₁) (H := P.C₂) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν) (d := (P.d : ℝ))
      (ρ := (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) (g := (π.gsb : ℝ)) (R := (R : ℝ))
      π.Gsb.order (by linarith [hs.c1_ge]) (by linarith [hs.c1_ge, hs.c1_le_c2]) hs.c1_le_c2
      hs.delta_pos hs.delta_le hL1 hν0 hs.nu_small hs.cost (by positivity) (by exact_mod_cast hR)
      (by simpa [Fama.Stage1PieceGD.gsb, hDdef, Fama.Stage1PieceG.data] using hc)
      (by simpa [hDdef, Fama.Stage1PieceG.data] using hf)
    simpa [hM] using this
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (by linarith [hs.c1_ge, hs.c1_le_c2]) (Real.exp_pos _).le
  have hnorm : ‖val‖ ≤ (∫ ξ, ‖w ξ‖ ∂μ) * M := by
    rw [hv]
    have h := norm_integral_le_of_norm_le (hwint.mul_const M)
      (Filter.Eventually.of_forall (fun ξ => by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hKle ξ) (norm_nonneg _))))
    simpa only [integral_mul_const] using h
  have hW0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun ξ => norm_nonneg _
  have hW1 : 0 ≤ (∫ ξ, ‖w ξ‖ ∂μ) / s := div_nonneg hW0 hs0.le
  have hwb : (∫ ξ, ‖w ξ‖ ∂μ) / s ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := by
    rw [div_le_iff₀ hs0]; exact hwbound
  have hcls := class_piece_bound (C := P.C₁) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν)
    (n := n) (nsb := π.Gsb.order) (R := R) (m := π.Gsb.order + 2 * R) (W := (∫ ξ, ‖w ξ‖ ∂μ) / s) (X := M) (H := P.C₂)
    (gsk := (π.gsk : ℝ)) (bsk := (π.bsk : ℝ)) (qsk := (π.Cs.hinges.card : ℝ))
    (gsb := (π.gsb : ℝ)) (ρsb := (π.Gsb.molecule.rho : ℝ))
    hs.c1_ge hs.delta_pos hs.delta_le hL1 hs.nu_pos (by linarith [hs.nu_small]) hs.nu_eta
    hs.eta_pos hs.eta_le hnsb (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith [hs.c1_ge, hs.c1_le_c2]) hW1 hM0
    hwb (by rw [hM])
  calc ‖val‖ ≤ (∫ ξ, ‖w ξ‖ ∂μ) * M := hnorm
    _ = s * (((∫ ξ, ‖w ξ‖ ∂μ) / s) * M) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcls hs0.le

/-- TARGET L2236-L2255 for the integral conjunct of `Represents` alone (R23 (2)); the centre loss `C_1^{n_sb}`
of R24 D3 is absorbed as `C_1^{n_sb + 2R} <= C_1^{5n}` (using `R <= 2n`, from the bond count of a sound piece) into the per-node factor `C_1^6 delta^{10 nu}`. -/
theorem stage1_sum_bound_int_gamma (P : WTParams) (hs : PieceSmall P)
    (hcoarse : Famc.CoarseSplicedGammaAt P) (hfine : Famc.FineSplicedChoicesGammaAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Fama.Stage1DataG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) [Fintype Cl] (_cls : S.Pc → Cl) (s : ℝ) (hs0 : 0 < s)
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
  let := S.fin
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hpiece : ∀ π, ‖S.val π / (s : ℂ)‖ ≤ P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
      (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    intro π
    have h := stage1_piece_bound_int_gamma P hs hcoarse hfine hp hR hRmax (S.piece π) tt base roots
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
      simp only [Fama.Stage1PieceGD.gbar, Fama.Stage1PieceGD.rbar, Nat.cast_add]
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

/-- TARGET (finalprooffin2), L2253-L2255, for the integral conjunct of `Represents` alone (R23 (2)). The
centre loss `C_1^{n_sb}` (R24 D3) is absorbed per node: the hypothesis `hδ` is
`6 C_0 C_1^6 delta^{2 nu} <= 1`. -/
theorem stage1_core_bound_int_gamma (P : WTParams) (hs : PieceSmall P)
    (hcoarse : Famc.CoarseSplicedGammaAt P) (hfine : Famc.FineSplicedChoicesGammaAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Fama.Stage1DataG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) [Fintype Cl] (cls : S.Pc → Cl) (s : ℝ) (hs0 : 0 < s)
    (hsound : ∀ π, (S.piece π).Sound p base roots)
    (hnsb : ∀ π, (S.piece π).Gsb.order ≤ n)
    (hrep : ∀ π, (S.piece π).RepresentsInt n tt base roots s (S.val π))
    (hrb : ∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ n)
    (hgb : ∀ π, (S.piece π).gbar ≤ n)
    (hpc : ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ n * (C₀ : ℝ) ^ n * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r))
    (hδ : ((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν) ≤ 1)
    (hT2 : P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2)
    (hS2 : (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2)
    (hL : 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) ≤
      P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s *
      (P.δ ^ (8 * P.ν * n) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
  have h := stage1_sum_bound_int_gamma P hs hcoarse hfine hp hR hRmax S tt base roots C₀ Cl cls s hs0
    hsound hnsb hrep hrb hgb hpc hT2 hS2
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hs0.le)
  set Y : ℝ := 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) with hY
  have hY0 : 0 ≤ Y := by
    have hC₂ : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    rw [hY]; positivity
  have hδ0 := hs.delta_pos
  have hpow : (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * ((6 * C₀ : ℕ) : ℝ) ^ n = (((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) ^ n *
      P.δ ^ (8 * P.ν * n) := by
    have h8 : P.δ ^ (8 * P.ν * (n : ℝ)) = (P.δ ^ (8 * P.ν)) ^ n := Real.rpow_mul_natCast hδ0.le _ _
    have h10 : P.δ ^ (10 * P.ν) = P.δ ^ (2 * P.ν) * P.δ ^ (8 * P.ν) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    rw [h8, ← mul_pow, ← mul_pow, h10]
    congr 1; ring
  have hrearr : 4 * (P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))) =
      ((P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * ((6 * C₀ : ℕ) : ℝ) ^ n) * Y := by
    rw [hY]; ring
  rw [hrearr, hpow]
  have hn1 : (((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) ^ n ≤ 1 := pow_le_one₀ (by
    have := hs.c1_ge
    positivity) hδ
  have hδ8 : 0 ≤ P.δ ^ (8 * P.ν * (n : ℝ)) := Real.rpow_nonneg hδ0.le _
  calc (((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) ^ n * P.δ ^ (8 * P.ν * (n : ℝ)) * Y
      ≤ 1 * P.δ ^ (8 * P.ν * (n : ℝ)) * Y := by gcongr
    _ = P.δ ^ (8 * P.ν * (n : ℝ)) * Y := by ring
    _ ≤ P.δ ^ (8 * P.ν * n) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :=
        mul_le_mul_of_nonneg_left hL hδ8

/-- TARGET (finalprooffin2), L2253-L2255: `stage1_core_bound_int` for the full `Represents`. -/
theorem stage1_core_bound_gamma (P : WTParams) (hs : PieceSmall P)
    (hcoarse : Famc.CoarseSplicedGammaAt P) (hfine : Famc.FineSplicedChoicesGammaAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Fama.Stage1DataG P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
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
    (hδ : ((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν) ≤ 1)
    (hT2 : P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2)
    (hS2 : (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2)
    (hL : 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) ≤
      P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s *
      (P.δ ^ (8 * P.ν * n) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) :=
  stage1_core_bound_int_gamma P hs hcoarse hfine hp hR hRmax S tt base roots C₀ Cl cls s hs0
    hsound hnsb (fun π => (hrep π).2) hrb hgb hpc hδ hT2 hS2 hL

/-- Main's `stage1_type_bound` over `𝒱_γ`. -/
theorem stage1_type_bound_gamma (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : Famc.CoarseSplicedGammaAt P) (hfine : Famc.FineSplicedChoicesGammaAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d)
    (hgate : Fama.Stage1ReductionGammaAt C₀ P)
    {p R N : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N)
    (hN : N ≤ P.N (p + 1) ^ 4) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (U : TypeFamily P (2 * R)) (s : ℝ) (hs0 : 0 < s) (hU : U.Bounded p)
    (hsize : ∀ LG ∈ A, U.toLF.size LG ≤ s) :
    ‖∑ LG ∈ A, U.toLF.value tt base roots LG‖ ≤ s *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
  have hctrl : ∀ LG ∈ A, U.toLF.Controlled LG := fun LG hLG =>
    U.controlled_of_bounded hU LG (Canon.layer_le_of_isCanonGC (hA LG hLG).1)
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcounts⟩ :=
    hgate p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hU hsize
  let := S.fin
  let := hCl
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hsumm : ∀ LG ∈ A, ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (U.toLF.H LG j) (fun b => tt b.1.1) 0 base κ := by
    intro LG hLG j
    have hplain : LG.garden.IsPlain := (hA LG hLG).1.1
    exact summable_leafKernel_summand P.L P.γ P.δ LG (U.toLF.H LG j) _ 0 base roots 0
      (card_lone_le_one_of_plain LG.garden hplain)
      ((hctrl LG hLG j).summable_coset hd hL1 base)
  have hsum : ∑ LG ∈ A, U.toLF.value tt base roots LG = ∑ π, S.val π := by
    rw [sum_eq_sum_pieces roots A members cls sel hpart tt base U.toLF hsumm]
    exact Finset.sum_congr rfl fun π _ => ((hrep π).1).symm
  rw [hsum]
  have hnn : 0 ≤ s * (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    have := hs.delta_pos
    positivity
  by_cases hne : Nonempty S.Pc
  · obtain ⟨π⟩ := hne
    have hRN : R ≤ 2 * N := by
      have h1 := (hsound π).bond_count
      have h2 := hord π
      omega
    have hNlog : (N : ℝ) ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * P.D + 2)) := by
      have h1 : (N : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hN
      exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
    obtain ⟨hT2, hS2, hL⟩ := habs.2 N R hR hRN hNlog
    exact stage1_core_bound_gamma P hs hcoarse hfine hp hR hRmax S base roots C₀ tt Cl cls members sel U.toLF s hs0
      hsound hord (fun π => (hrep π)) hcounts.1 hcounts.2.1 hcounts.2.2 habs.1 hT2 hS2 hL
  · have hemp : IsEmpty S.Pc := not_nonempty_iff.mp hne
    simpa [Finset.univ_eq_empty] using hnn

/-- The waist from the `𝒱_γ` gates at one parameter record: L5a's Stage 1 reduction over `𝒱_γ`, L5c's finalsbest1
over `𝒱_γ`, the finalsbest2 estimate over `𝒱_γ` (`Famc.FineSplicedChoicesGammaAt`) and the numerics. -/
theorem typeGateAt_of_gamma (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : Famc.CoarseSplicedGammaAt P) (hfine : Famc.FineSplicedChoicesGammaAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d)
    (hgate : Fama.Stage1ReductionGammaAt C₀ P) : TypeGateAt P :=
  fun hp hR hRmax hN1 hN A hA hcl tt htt base roots U s hs0 hU hsize =>
    stage1_type_bound_gamma C₀ P hs hcoarse hfine habs hlog hd hgate hp hR hRmax hN1 hN A hA hcl tt htt
      base roots U s hs0 hU hsize

/-- The numerical side conditions of the counting cover (`Famc.CoverSmall`) are fields of `PieceSmall`. -/
theorem coverSmall_of_pieceSmall {P : WTParams} (hs : PieceSmall P) : Famc.CoverSmall P :=
  ⟨hs.L_ge, hs.delta_pos, hs.c1_ge, hs.delta_le, hs.cap, hs.cap_le, hs.delta_exp, hs.scale_log, hs.count_const⟩

end WaveTurbulence.GammaLow.LGLow
