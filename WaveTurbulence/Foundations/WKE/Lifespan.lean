/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.IsWKESolution

/-!
# The maximal time of existence `τ_max`

* `WaveTurbulence.WKE.tauMax φin := sup {τ★ > 0 : (WKE) has a Schwartz solution on [0, τ★]}`
  (in `ℝ≥0∞`), the `τ_max` of TARGET Prop `wkelwp` (L598–L601).
* `IsWKESolution.mono`: restriction of a solution to a shorter interval.
* `IsWKESolution.glue`: a solution on `[0, T]` followed by a solution on `[0, ε]` with data
  `φ(T)` gives a solution on `[0, T + ε]`.
* `WKE.exists_isWKESolution_of_lt_tauMax`: the `→` direction of `wkelwp` conjunct 1.

The `←` direction (a solution on the closed `[0, τ★]` extends past `τ★`) and `0 < tauMax` follow
from local existence (`WaveTurbulence.WKE.lt_tauMax_iff`, `WKE.tauMax_pos` in `WKE/Existence`).
-/

public section

open Set
open scoped SchwartzMap ENNReal

namespace WaveTurbulence

variable {d : ℕ}

/-- Restriction of a Schwartz solution to a shorter interval. -/
theorem IsWKESolution.mono {φin : 𝓢(Mom d, ℝ)} {T T' : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (h : IsWKESolution φin T' φ) (hT : T ≤ T') : IsWKESolution φin T φ := by
  have hsub : Icc 0 T ⊆ Icc 0 T' := Icc_subset_Icc le_rfl hT
  exact ⟨h.1.mono hsub, h.2.1, fun τ hτ k => (h.2.2 τ (hsub hτ) k).mono hsub⟩

/-- The concatenation of `φ` on `[0, T]` and `ψ(· - T)` on `[T, T + ε]`. -/
@[expose] noncomputable def glueSol (T : ℝ) (φ ψ : ℝ → 𝓢(Mom d, ℝ)) (τ : ℝ) : 𝓢(Mom d, ℝ) :=
  if τ ≤ T then φ τ else ψ (τ - T)

/-- **Gluing** two Schwartz solutions. -/
theorem IsWKESolution.glue {φin : 𝓢(Mom d, ℝ)} {T ε : ℝ} {φ ψ : ℝ → 𝓢(Mom d, ℝ)}
    (hT : 0 ≤ T) (hε : 0 ≤ ε) (hφ : IsWKESolution φin T φ) (hψ : IsWKESolution (φ T) ε ψ) :
    IsWKESolution φin (T + ε) (glueSol T φ ψ) := by
  have hsplit : Icc 0 (T + ε) = Icc 0 T ∪ Icc T (T + ε) :=
    (Icc_union_Icc_eq_Icc hT (by linarith)).symm
  have e1 : ∀ τ ∈ Icc 0 T, glueSol T φ ψ τ = φ τ := fun τ hτ => if_pos hτ.2
  have e2 : ∀ τ ∈ Icc T (T + ε), glueSol T φ ψ τ = ψ (τ - T) := by
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with h | h
    · subst h; simp [glueSol, hψ.2.1]
    · exact if_neg (not_le.mpr h)
  have hmaps : MapsTo (fun τ => τ - T) (Icc T (T + ε)) (Icc 0 ε) := fun τ hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hφ.1.congr e1
    · refine ContinuousOn.congr ?_ e2
      exact hψ.1.comp (continuousOn_id.sub continuousOn_const) hmaps
  · rw [e1 0 ⟨le_rfl, hT⟩, hφ.2.1]
  · intro τ hτ k
    rw [hsplit]
    refine HasDerivWithinAt.union ?_ ?_
    · by_cases h : τ ∈ Icc 0 T
      · rw [e1 τ h]
        exact (hφ.2.2 τ h k).congr_of_mem (fun σ hσ => by rw [e1 σ hσ]) h
      · have : τ ∉ closure (Icc 0 T) := by rwa [closure_Icc]
        exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr (HasFDerivWithinAt.of_notMem_closure this)
    · by_cases h : τ ∈ Icc T (T + ε)
      · rw [e2 τ h]
        have hd := (hψ.2.2 (τ - T) (hmaps h) k).comp τ ((hasDerivAt_id τ).sub_const T).hasDerivWithinAt
          hmaps
        simp only [mul_one] at hd
        exact hd.congr_of_mem (fun σ hσ => by rw [e2 σ hσ]; rfl) h
      · have : τ ∉ closure (Icc T (T + ε)) := by rwa [closure_Icc]
        exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr (HasFDerivWithinAt.of_notMem_closure this)

namespace WKE

/-- **`τ_max`** of TARGET Prop `wkelwp` (L598–L601): the supremum (in `ℝ≥0∞`) of the `τ★ > 0` such
that (WKE) has a Schwartz-class solution (`IsWKESolution`) on `[0, τ★]` with data `φin`. -/
@[expose] noncomputable def tauMax (φin : 𝓢(Mom d, ℝ)) : ℝ≥0∞ :=
  ⨆ (τ : ℝ) (_ : 0 < τ ∧ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τ φ), ENNReal.ofReal τ

theorem ofReal_le_tauMax {φin : 𝓢(Mom d, ℝ)} {τ : ℝ} (hτ : 0 < τ) {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin τ φ) : ENNReal.ofReal τ ≤ tauMax φin :=
  le_iSup₂_of_le (f := fun (τ : ℝ) (_ : 0 < τ ∧ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τ φ) =>
    ENNReal.ofReal τ) τ ⟨hτ, φ, hφ⟩ le_rfl

/-- `wkelwp` conjunct 1, `→`: below `τ_max` there is a Schwartz solution. -/
theorem exists_isWKESolution_of_lt_tauMax {φin : 𝓢(Mom d, ℝ)} {τstar : ℝ} (hτ : 0 < τstar)
    (h : ENNReal.ofReal τstar < tauMax φin) :
    ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ := by
  obtain ⟨τ', hτ'⟩ := lt_iSup_iff.mp h
  obtain ⟨⟨hτ'0, φ, hφ⟩, hlt⟩ := lt_iSup_iff.mp hτ'
  refine ⟨φ, hφ.mono ?_⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff hτ'0).mp hlt).le

end WKE

end WaveTurbulence
