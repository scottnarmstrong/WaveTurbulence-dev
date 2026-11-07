/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.NormSwapConj
import Mathlib.Tactic

/-!
# S2 REPRESENTS: swap-and-conjugate invariance of `XNorm00Restr` (finding F-CONJ)

The variant of `ConjCoh.XNorm_swapConj` for the vector-free norm `XNorm00` (arbitrary index type `V`),
used for the time factors `J` of the separated coherent app.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace WaveTurbulence.Represents

open WaveTurbulence WaveTurbulence.ConjCoh

variable {r : ℕ} {V : Type*}

/-- Permute the time coordinates and conjugate (arbitrary index type). -/
def swapConjV (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → V → ℂ) : (Fin r → ℝ) → V → ℂ :=
  fun t v => conj (F (permT π t) v)

theorem timeFT_swapConjV (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → V → ℂ) (lam : Fin r → ℝ)
    (v : V) : timeFT (swapConjV π F) lam v = conj (timeFT F (nuF π lam) v) := by
  unfold timeFT
  have key : ∀ t : Fin r → ℝ, swapConjV π F t v *
      Complex.exp (-(2 * Real.pi * ∑ i, lam i * t i : ℝ) * Complex.I) =
      (fun s : Fin r → ℝ => conj (F s v * Complex.exp
        (-(2 * Real.pi * ∑ i, nuF π lam i * s i : ℝ) * Complex.I))) (permT π t) := by
    intro t
    have hs : ∑ i, nuF π lam i * permT π t i = -∑ i, lam i * t i := by
      simp only [nuF, permT, neg_mul, Finset.sum_neg_distrib]
      congr 1
      exact Equiv.sum_comp π (fun i => lam i * t i)
    simp only [swapConjV, map_mul, hs]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key),
    (permT_mp π).integral_comp (permT_emb π) (fun s : Fin r → ℝ => conj (F s v * Complex.exp
        (-(2 * Real.pi * ∑ i, nuF π lam i * s i : ℝ) * Complex.I))), integral_conj]

theorem integrable_swapConjV (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → V → ℂ) (v : V)
    (h : Integrable fun t => F t v) : Integrable fun t => swapConjV π F t v := by
  have h1 : Integrable (fun s => conj (F s v)) := by
    simpa using (Complex.conjCLE.integrable_comp_iff (φ := fun s => F s v) (μ := volume)).2 h
  exact ((permT_mp π).integrable_comp_emb (permT_emb π)).2 h1

theorem swapConjV_swapConjV {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i)
    (F : (Fin r → ℝ) → V → ℂ) : swapConjV π (swapConjV π F) = F := by
  funext t v; simp [swapConjV, permT_permT_of_invol hπ]

open Classical in
theorem XNorm00_swapConjV_le (π : Equiv.Perm (Fin r)) (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ (swapConjV π F) ≤ XNorm00 θ F := by
  unfold XNorm00
  by_cases hF : ∀ v, Integrable fun t => F t v
  · have hF' : ∀ v, Integrable fun t => swapConjV π F t v := fun v => integrable_swapConjV π F v (hF v)
    have hpt : ∀ lam : Fin r → ℝ, maxBracketPow θ lam * ⨆ v, ‖timeFT (swapConjV π F) lam v‖ₑ =
        (fun μ : Fin r → ℝ => maxBracketPow θ μ * ⨆ v, ‖timeFT F μ v‖ₑ) (nuF π lam) := by
      intro lam
      simp only [maxBracketPow_nuF, timeFT_swapConjV, enorm_eq_nnnorm, RCLike.nnnorm_conj]
    rw [if_pos hF', if_pos hF, lintegral_congr hpt]
    exact le_of_eq ((nuF_mp π).lintegral_comp_emb (nuF_emb π)
      (fun μ : Fin r → ℝ => maxBracketPow θ μ * ⨆ v, ‖timeFT F μ v‖ₑ))
  · rw [if_neg hF]; exact le_top

theorem XNorm00_swapConjV {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i) (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) : XNorm00 θ (swapConjV π F) = XNorm00 θ F := by
  refine le_antisymm (XNorm00_swapConjV_le π θ F) ?_
  have := XNorm00_swapConjV_le π θ (swapConjV π F)
  rwa [swapConjV_swapConjV hπ] at this

theorem XNorm00Restr_swapConjV {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i) (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ B K (swapConjV π F) = XNorm00Restr θ (permT π ⁻¹' B) K F := by
  unfold XNorm00Restr
  apply le_antisymm
  · refine le_iInf fun G => le_iInf fun hG => ?_
    have hc : ∀ t ∈ B, ∀ v ∈ K, swapConjV π G t v = swapConjV π F t v := by
      intro t ht v hv
      have := hG (permT π t) (by simpa [Set.mem_preimage, permT_permT_of_invol hπ] using ht) v hv
      simp only [swapConjV, this]
    exact iInf_le_of_le (swapConjV π G) (iInf_le_of_le hc (XNorm00_swapConjV hπ θ G).le)
  · refine le_iInf fun G => le_iInf fun hG => ?_
    have hc : ∀ s ∈ permT π ⁻¹' B, ∀ v ∈ K, swapConjV π G s v = F s v := by
      intro s hs v hv
      have := hG (permT π s) hs v hv
      simp only [swapConjV, this]
      simp [permT_permT_of_invol hπ]
    exact iInf_le_of_le (swapConjV π G) (iInf_le_of_le hc (XNorm00_swapConjV hπ θ G).le)

end WaveTurbulence.Represents
