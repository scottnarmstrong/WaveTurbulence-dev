/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# Invariance of `XNorm`, `XNormRestr` under a time permutation and complex conjugation (CONJ-COH)

For a permutation `π` of the time coordinates, `permT π t = t ∘ π`, and `swapConj π F (t, k) = conj (F (t ∘ π, k))`.
The time Fourier transform of `swapConj π F` is `conj ∘ (timeFT F) ∘ (λ ↦ -(λ ∘ π))`; the map `λ ↦ -(λ ∘ π)`
preserves Lebesgue measure and `maxBracketPow`, conjugation preserves `‖·‖` and commutes with `∂_k`.
Hence `XNorm` (F80 guard included: both parts are invariant) is unchanged when `π` is an involution
(`XNorm_swapConj`), and `XNormRestr` over `B` becomes `XNormRestr` over `permT π ⁻¹' B` (`XNormRestr_swapConj`).
With `π = Equiv.swap 0 1` on `Fin 2` this is the swap `(t, s) ↦ (s, t)` plus conjugation of V5 (R20(5)).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace WaveTurbulence.ConjCoh

open WaveTurbulence

variable {r d : ℕ}

/-- Permute the time coordinates: `(permT π t) i = t (π i)`. -/
def permT (π : Equiv.Perm (Fin r)) (t : Fin r → ℝ) : Fin r → ℝ := fun i => t (π i)

/-- The frequency map `λ ↦ -(λ ∘ π)` appearing in the Fourier transform of `swapConj π F`. -/
def nuF (π : Equiv.Perm (Fin r)) (lam : Fin r → ℝ) : Fin r → ℝ := fun j => -lam (π j)

/-- Permute the time coordinates and conjugate. -/
def swapConj (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → Mom d → ℂ) : (Fin r → ℝ) → Mom d → ℂ :=
  fun t k => conj (F (permT π t) k)

theorem permE (π : Equiv.Perm (Fin r)) :
    ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℝ) π.symm) = permT π := by
  funext t i
  simp [permT, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

theorem permT_mp (π : Equiv.Perm (Fin r)) : MeasurePreserving (permT π) volume volume := by
  rw [← permE]; exact volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℝ) π.symm

theorem permT_emb (π : Equiv.Perm (Fin r)) : MeasurableEmbedding (permT π) := by
  rw [← permE]; exact (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℝ) π.symm).measurableEmbedding

theorem nuF_eq (π : Equiv.Perm (Fin r)) : nuF π = Neg.neg ∘ permT π := by
  funext lam j; simp [nuF, permT]

theorem nuF_mp (π : Equiv.Perm (Fin r)) : MeasurePreserving (nuF π) volume volume := by
  rw [nuF_eq]; exact (Measure.measurePreserving_neg _).comp (permT_mp π)

theorem nuF_emb (π : Equiv.Perm (Fin r)) : MeasurableEmbedding (nuF π) := by
  rw [nuF_eq]; exact (MeasurableEquiv.neg (Fin r → ℝ)).measurableEmbedding.comp (permT_emb π)

theorem permT_permT_of_invol {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i) (t : Fin r → ℝ) :
    permT π (permT π t) = t := by
  funext i; simp [permT, hπ]

theorem swapConj_swapConj {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i)
    (F : (Fin r → ℝ) → Mom d → ℂ) : swapConj π (swapConj π F) = F := by
  funext t k; simp [swapConj, permT_permT_of_invol hπ]

/-- The time Fourier transform of `swapConj π F`. -/
theorem timeFT_swapConj (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → Mom d → ℂ) (lam : Fin r → ℝ)
    (k : Mom d) : timeFT (swapConj π F) lam k = conj (timeFT F (nuF π lam) k) := by
  unfold timeFT
  have key : ∀ t : Fin r → ℝ, swapConj π F t k *
      Complex.exp (-(2 * Real.pi * ∑ i, lam i * t i : ℝ) * Complex.I) =
      (fun s : Fin r → ℝ => conj (F s k * Complex.exp
        (-(2 * Real.pi * ∑ i, nuF π lam i * s i : ℝ) * Complex.I))) (permT π t) := by
    intro t
    have hs : ∑ i, nuF π lam i * permT π t i = -∑ i, lam i * t i := by
      simp only [nuF, permT, neg_mul, Finset.sum_neg_distrib]
      congr 1
      exact Equiv.sum_comp π (fun i => lam i * t i)
    simp only [swapConj, map_mul, hs]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key),
    (permT_mp π).integral_comp (permT_emb π) (fun s : Fin r → ℝ => conj (F s k * Complex.exp
        (-(2 * Real.pi * ∑ i, nuF π lam i * s i : ℝ) * Complex.I))), integral_conj]


theorem partialMom_conj (j : Fin d) (g : Mom d → ℂ) :
    partialMom j (fun k => conj (g k)) = fun k => conj (partialMom j g k) := by
  funext k
  have h := congrArg (fun L : Mom d →L[ℝ] ℂ => L (EuclideanSpace.single j 1))
    (ContinuousLinearEquiv.comp_fderiv Complex.conjCLE (f := g) (x := k))
  simpa [partialMom, Function.comp_def] using h

theorem partialMom_iter_conj (j : Fin d) (n : ℕ) (g : Mom d → ℂ) :
    (partialMom j)^[n] (fun k => conj (g k)) = fun k => conj ((partialMom j)^[n] g k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, partialMom_conj, Function.iterate_succ_apply']

theorem iterPartial_conj (ρ : Fin d → ℕ) (g : Mom d → ℂ) :
    iterPartial ρ (fun k => conj (g k)) = fun k => conj (iterPartial ρ g k) := by
  unfold iterPartial
  generalize List.finRange d = L
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.foldr_cons]
    rw [ih, partialMom_iter_conj]

theorem maxBracketPow_nuF (π : Equiv.Perm (Fin r)) (θ : ℝ) (lam : Fin r → ℝ) :
    maxBracketPow θ (nuF π lam) = maxBracketPow θ lam := by
  unfold maxBracketPow
  congr 3
  have : (fun i => Real.sqrt (1 + nuF π lam i ^ 2)) = fun i => (fun j => Real.sqrt (1 + lam j ^ 2)) (π i) := by
    funext i; simp [nuF]
  rw [this]
  exact π.iSup_comp (g := fun j => Real.sqrt (1 + lam j ^ 2))


theorem timeFT_swapConj_fun (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → Mom d → ℂ) (lam : Fin r → ℝ) :
    timeFT (swapConj π F) lam = fun k => conj (timeFT F (nuF π lam) k) := by
  funext k; exact timeFT_swapConj π F lam k

theorem integrable_swapConj (π : Equiv.Perm (Fin r)) (F : (Fin r → ℝ) → Mom d → ℂ) (k : Mom d)
    (h : Integrable fun t => F t k) : Integrable fun t => swapConj π F t k := by
  have h1 : Integrable (fun s => conj (F s k)) := by
    simpa using (Complex.conjCLE.integrable_comp_iff (φ := fun s => F s k) (μ := volume)).2 h
  exact ((permT_mp π).integrable_comp_emb (permT_emb π)).2 h1

open Classical in
/-- One direction of the invariance (no involution hypothesis needed). -/
theorem XNorm_swapConj_le (π : Equiv.Perm (Fin r)) (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ Λ₁ Λ₂ (swapConj π F) ≤ XNorm θ Λ₁ Λ₂ F := by
  unfold XNorm
  by_cases hF : (∀ k, Integrable fun t => F t k) ∧
      (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam))
  · have hF' : (∀ k, Integrable fun t => swapConj π F t k) ∧
        (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT (swapConj π F) lam)) := by
      refine ⟨fun k => integrable_swapConj π F k (hF.1 k), ?_⟩
      rcases hF.2 with h0 | hae
      · exact Or.inl h0
      · right
        have := (nuF_mp π).quasiMeasurePreserving.ae hae
        filter_upwards [this] with lam hl
        rw [timeFT_swapConj_fun]
        exact Complex.conjCLE.contDiff.comp hl
    have hp : ∀ ρ : Fin d → ℕ, ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam *
        ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT (swapConj π F) lam) k‖) =
        ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam *
        ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖) := by
      intro ρ
      have hpt : ∀ lam : Fin r → ℝ, maxBracketPow θ lam *
          ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT (swapConj π F) lam) k‖) =
          (fun μ : Fin r → ℝ => maxBracketPow θ μ *
            ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F μ) k‖)) (nuF π lam) := by
        intro lam
        simp only [maxBracketPow_nuF, timeFT_swapConj_fun, iterPartial_conj, RCLike.norm_conj]
      rw [lintegral_congr hpt]
      exact (nuF_mp π).lintegral_comp_emb (nuF_emb π) (fun μ : Fin r → ℝ => maxBracketPow θ μ *
            ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F μ) k‖))
    split_ifs with h1
    · exact le_of_eq (iSup_congr fun ρ => iSup_congr fun _ => hp ρ)
    · exact absurd hF' h1
  · split_ifs <;> exact le_top

/-- **`XNorm` is invariant under a time-coordinate involution plus complex conjugation** (the F80 guard
is symmetric). -/
theorem XNorm_swapConj {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i) (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ Λ₁ Λ₂ (swapConj π F) = XNorm θ Λ₁ Λ₂ F := by
  refine le_antisymm (XNorm_swapConj_le π θ Λ₁ Λ₂ F) ?_
  have := XNorm_swapConj_le π θ Λ₁ Λ₂ (swapConj π F)
  rwa [swapConj_swapConj hπ] at this

/-- **`XNormRestr` over `B` of `swapConj π F` is `XNormRestr` of `F` over the preimage box.** -/
theorem XNormRestr_swapConj {π : Equiv.Perm (Fin r)} (hπ : ∀ i, π (π i) = i) (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B K (swapConj π F) = XNormRestr θ Λ₁ Λ₂ (permT π ⁻¹' B) K F := by
  unfold XNormRestr
  apply le_antisymm
  · refine le_iInf fun G => le_iInf fun hG => ?_
    have hc : ∀ t ∈ B, ∀ k ∈ K, swapConj π G t k = swapConj π F t k := by
      intro t ht k hk
      have := hG (permT π t) (by simpa [Set.mem_preimage, permT_permT_of_invol hπ] using ht) k hk
      simp only [swapConj, this]
    exact iInf_le_of_le (swapConj π G) (iInf_le_of_le hc (XNorm_swapConj hπ θ Λ₁ Λ₂ G).le)
  · refine le_iInf fun G => le_iInf fun hG => ?_
    have hc : ∀ s ∈ permT π ⁻¹' B, ∀ k ∈ K, swapConj π G s k = F s k := by
      intro s hs k hk
      have := hG (permT π s) hs k hk
      simp only [swapConj, this]
      simp [permT_permT_of_invol hπ]
    exact iInf_le_of_le (swapConj π G) (iInf_le_of_le hc (XNorm_swapConj hπ θ Λ₁ Λ₂ G).le)

end WaveTurbulence.ConjCoh
