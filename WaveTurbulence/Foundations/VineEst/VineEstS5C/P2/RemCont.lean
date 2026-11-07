/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.RemAe
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space

/-! # P2: the continuous witness of a gate remainder (step 3; the continuity ruling)

`restr_ae_cont`: a scalar time factor with finite `XNorm00Restr` on `B` is a.e. on `B` equal to a continuous function.
`remainder_ae_cont`: `f = K - ∑_i c_i J_i M_i` on `B` (`K` continuous in time for each `k`, finite `XNorm00Restr` of each `J_i`,
`M_i` any functions of `k`) agrees a.e. on `B`, for all `k` simultaneously, with a function continuous in time. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.NormBridgeScratch MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem restr_ae_cont {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} {J : (Fin r → ℝ) → ℂ}
    (h : XNorm00Restr (V := Unit) θ B Set.univ (fun ts _ => J ts) < ⊤) :
    ∃ J' : (Fin r → ℝ) → ℂ, Continuous J' ∧ ∀ᵐ t, t ∈ B → J t = J' t := by
  unfold XNorm00Restr at h
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 h
  obtain ⟨hGB, hGn⟩ := iInf_lt_iff.1 hG
  set g : (Fin r → ℝ) → ℂ := fun t => G t () with hg
  have hgn : timeFourierNorm θ g < ⊤ := by
    have : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [this]; exact lt_of_lt_of_le hGn le_top
  obtain ⟨hc, hae, -⟩ := Regref.rep_props hθ hgn
  refine ⟨Regref.rep g, hc, ?_⟩
  filter_upwards [hae] with t ht htB
  rw [ht]
  exact (hGB t htB () (Set.mem_univ _)).symm

/-- Finite sums of separated terms: the continuous time-representative of the remainder. -/
theorem remainder_ae_cont {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin 2 → ℝ)} {m : ℕ} (c : ℂ)
    (K f : (Fin 2 → ℝ) → Mom d → ℂ) (J : Fin m → (Fin 2 → ℝ) → ℂ) (M : Fin m → Mom d → ℝ)
    (hK : ∀ k, Continuous fun t => K t k)
    (hJ : ∀ i, XNorm00Restr (V := Unit) θ B Set.univ (fun ts _ => J i ts) < ⊤)
    (hf : ∀ t ∈ B, ∀ k, f t k = K t k - ∑ i, c * J i t * (M i k : ℂ)) :
    ∃ f' : (Fin 2 → ℝ) → Mom d → ℂ, (∀ k, Continuous fun t => f' t k) ∧ ∀ᵐ t, t ∈ B → ∀ k, f t k = f' t k := by
  choose J' hJc hJae using fun i => restr_ae_cont hθ (hJ i)
  refine ⟨fun t k => K t k - ∑ i, c * J' i t * (M i k : ℂ), fun k => ?_, ?_⟩
  · refine (hK k).sub (continuous_finset_sum _ fun i _ => ?_)
    exact (continuous_const.mul (hJc i)).mul continuous_const
  · have hall : ∀ᵐ t, ∀ i, t ∈ B → J i t = J' i t := ae_all_iff.2 hJae
    filter_upwards [hall] with t ht htB k
    rw [hf t htB k]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [ht i htB]

end WaveTurbulence.VineEstS5C.P2
