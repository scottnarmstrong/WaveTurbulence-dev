/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Embed
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Coef
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Joint
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Ae
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Engine

/-! # Row builders for the arity-3 engine (V5 Step 4d-A, item 2)

* `rowModes3_of_restr`: an `r`-independent two-clock row with a restriction-norm bound has three-clock coefficients
  (zero third mode) with the `fs_expansion` bound.
* `hasSum_sepCoef`: pointwise expansion of a separated row `H(c) M(r,k)` from the expansion of `H`.
* `ae_clock_of_ae`: an a.e. statement on the three clocks of a row whose three slots are distinct internal times
  pulls back to an a.e. statement in the internal times `τ` (the form of `hser` in `clockedBoundMix3`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3Par.Eng
 WaveTurbulence.VineEstS3.Eng MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem SNorm_zero_fun (A B : ℕ) : SNorm A B (fun _ : Mom d => (0 : ℂ)) = 0 := by
  have := SNorm_smul_le (d := d) A B 0 (fun _ => 0)
  simpa using this

/-- **Two-clock rows without `r`-dependence, embedded in the arity-3 engine.** -/
theorem rowModes3_of_restr {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f t k) →
      XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      ∃ c : (Fin 3 → ℤ) → Mom d → ℂ,
        (∀ t3 : Fin 3 → ℝ, ![t3 0, t3 1] ∈ B → ∀ k, HasSum (fun m : Fin 3 → ℤ => c m k * fsPhase m t3)
          (f ![t3 0, t3 1] k)) ∧
        ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≤ C * b := by
  obtain ⟨C, hC, hf⟩ := fs_expansion (r := 2) (d := d) hθ hΛ
  refine ⟨C, hC, fun q B f b hBc hBi hfc hb => ?_⟩
  obtain ⟨c2, h1, h2⟩ := hf q B Set.univ f b hBc hBi (fun k _ => hfc k) hb
  refine ⟨fun m k => embed2 (fun n => c2 n k) m, fun t3 ht3 k => ?_, ?_⟩
  · exact hasSum_embed2 (fun n => c2 n k) t3 (h1 _ ht3 k (Set.mem_univ k))
  · refine le_trans (le_of_eq ?_) h2
    rw [← embedMode_injective.tsum_eq (f := fun m : Fin 3 → ℤ => maxBracketPow θ (half m) *
      SNorm Λ₁ Λ₂ (fun k => embed2 (fun n => c2 n k) m))]
    · refine tsum_congr fun n => ?_
      rw [maxBracketPow_embedMode]
      congr 2
      funext k
      rw [embed2_embedMode]
    · intro m hm
      by_contra hnr
      apply hm
      have : (fun k => embed2 (fun n => c2 n k) m) = fun _ => 0 := funext fun k => embed2_eq_zero _ m hnr
      simp [this, SNorm_zero_fun]

/-- A separated row expands pointwise from the expansion of its time factor. -/
theorem hasSum_sepCoef {h : (Fin 3 → ℤ) → ℂ} {t : Fin 3 → ℝ} {S : ℂ}
    (hS : HasSum (fun m : Fin 3 → ℤ => h m * fsPhase m t) S) (M : Mom d → Mom d → ℂ) (r k : Mom d) :
    HasSum (fun m : Fin 3 → ℤ => sepCoef h M m r k * fsPhase m t) (S * M r k) := by
  have := hS.mul_right (M r k)
  convert this using 2 with m
  unfold sepCoef; ring

/-- Pull an a.e. statement on the clocks of a row with three distinct internal slots back to the internal times. -/
theorem ae_clock_of_ae {D : SumintPar.SumintDatum d} (cr : ClockedRows3 D) (ρ : Row D) (tt : Fin 3 → ℝ)
    (v : Fin 3 → D.S.TVar) (hv : Function.Injective v) (hs : ∀ i, cr.slot ρ i = Sum.inl (v i))
    {P : (Fin 3 → ℝ) → Prop} (h : ∀ᵐ x : Fin 3 → ℝ, P x) :
    ∀ᵐ τ : D.S.TVar → ℝ, P (cr.clock τ tt ρ) := by
  have := ae_pullback_coords v hv h
  refine this.mono fun τ hτ => ?_
  convert hτ using 2
  simp [ClockedRows3.clock, VineEstS3Par.Eng.slotVal, hs _]

/-- **The joint three-clock row of clause (c).**  Time part `H(τ₀,τ₁,τ₂) = |τ₀-τ₁|^{-(1-3η)} (J(τ₀,τ₂) - J(τ₁,τ₂))`
(two-clock `J` with `𝔛^{1-η,0,0}` bound `β` on `B₂`), spatial part a function `M(r,k)` with a uniform-in-`r`
`S^{A,B}` bound.  The three-clock coefficients `c m r k = ĥ_m M(r,k)` expand the row `H M` a.e. on the box `B₃`, with
`coefBound θ A B c ≤ C β sup_r ‖M(r)‖_S`. -/
theorem jointRow_modes {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (J : (Fin 2 → ℝ) → ℂ) (B2 : Set (Fin 2 → ℝ)) (B3 : Set (Fin 3 → ℝ))
      (q : Fin 3 → ℝ) (β : ℝ≥0∞) (M : Mom d → Mom d → ℂ) (A B : ℕ),
      β ≠ ⊤ → B3 ⊆ cell q → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ R) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr (V := Unit) (1 - η) B2 Set.univ (fun ts _ => J ts) < β →
      ∃ c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ,
        (∀ᵐ τ : Fin 3 → ℝ, τ ∈ B3 → ∀ r k : Mom d, HasSum (fun m : Fin 3 → ℤ => c m r k * fsPhase m τ)
          ((((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (J ![τ 0, τ 2] - J ![τ 1, τ 2])) * M r k)) ∧
        coefBound θ A B c ≤ C * β * ⨆ r : Mom d, SNorm A B (M r) := by
  obtain ⟨C, hC, hJ⟩ := jointTime_modes hη0 hη4 hθ0 hθη R
  refine ⟨C, hC, fun J B2 B3 q β M A B hβ hc hi hR hB hlt => ?_⟩
  obtain ⟨ĥ, hae, hsum⟩ := hJ J B2 B3 q β hβ hc hi hR hB hlt
  refine ⟨sepCoef ĥ M, ?_, ?_⟩
  · filter_upwards [hae] with τ hτ htB r k
    exact hasSum_sepCoef (hτ htB) M r k
  · refine (coefBound_sep_le θ A B ĥ M).trans ?_
    exact mul_le_mul_left hsum _

end WaveTurbulence.VineEstS5A
