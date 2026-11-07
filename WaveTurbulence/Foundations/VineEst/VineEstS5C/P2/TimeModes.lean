/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Rows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ThetaMono
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BoxFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.TimeDomMeas
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-! # P2: Fourier modes of a scalar time factor (4d-A item (i), time part)

* `XNorm00_mono_theta`: monotonicity of the scalar `XNorm00` in `θ`;
* **`scalar_modes`**: for `J` with `‖J‖_{𝔛^{θ',0,0}(B)} < β` on a unit box `B` (`θ ≤ θ'`), `J(t) = ∑_m ĥ_m e^{πi m·t}` for a.e.
  `t ∈ B` with `∑_m ⟨m/2⟩^θ |ĥ_m| ≤ C β` (`C` depends on `θ, r` only) -- the `r`-clock version of `jointTime_modes` without
  the time difference;
* `embed2`-version `scalar2_modes3`: the two-clock expansion as a three-clock one with a zero third mode;
* `ae_clock_box`: an a.e. statement on `ℝⁿ` pulled back along an injective choice of internal times, restricted to the time
  domain, gives the `Ae` form of the engine. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.NormBridgeScratch MeasureTheory Set
open scoped ENNReal

theorem XNorm00_mono_theta {r : ℕ} {V : Type*} {θ θ' : ℝ} (h : θ ≤ θ') (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ F ≤ XNorm00 θ' F := by
  classical
  unfold XNorm00
  split_ifs with hc
  · refine lintegral_mono fun lam => ?_
    exact mul_le_mul_left (VineEstS3.maxBracketPow_mono h lam) _
  · exact le_rfl

theorem XNorm00Restr_mono_theta {r : ℕ} {V : Type*} {θ θ' : ℝ} (h : θ ≤ θ') (B : Set (Fin r → ℝ)) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) : XNorm00Restr θ B K F ≤ XNorm00Restr θ' B K F := by
  unfold XNorm00Restr
  refine le_iInf₂ fun G hG => ?_
  exact (iInf₂_le G hG).trans (XNorm00_mono_theta h G)

/-- **Fourier modes of a scalar time factor.** -/
theorem scalar_modes {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ : θ ≤ θ') (r : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (J : (Fin r → ℝ) → ℂ) (β : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) →
      XNorm00Restr (V := Unit) θ' B Set.univ (fun ts _ => J ts) < β →
      ∃ ĥ : (Fin r → ℤ) → ℂ,
        (∀ᵐ t : Fin r → ℝ, t ∈ B → HasSum (fun m : Fin r → ℤ => ĥ m * fsPhase m t) (J t)) ∧
        ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ‖ĥ m‖ₑ ≤ C * β := by
  obtain ⟨C, hC, hF⟩ := hcoef_sum_le (r := r) hθ
  refine ⟨C, hC, fun q B J β hc hi hJ => ?_⟩
  unfold XNorm00Restr at hJ
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hJ
  obtain ⟨hGB, hGn⟩ := iInf_lt_iff.1 hG
  set g : (Fin r → ℝ) → ℂ := fun t => G t () with hg
  have hmono : XNorm00 θ G ≤ XNorm00 θ' G := XNorm00_mono_theta hθθ G
  have hgn : timeFourierNorm θ g < ⊤ := by
    have : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [this]; exact lt_of_le_of_lt hmono (lt_of_lt_of_le hGn le_top)
  refine ⟨hcoef q g, ?_, ?_⟩
  · filter_upwards [scalar_fs_hasSum_ae hθ q hc hi hgn] with t ht htB
    have := ht htB
    simp only [hg] at this
    rwa [hGB t htB () (Set.mem_univ _)] at this
  · refine (hF q g).trans ?_
    have h1 : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [h1]
    exact mul_le_mul_right (hmono.trans hGn.le) _

/-- The two-clock expansion as a three-clock expansion (zero third mode). -/
theorem scalar2_modes3 {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ : θ ≤ θ') :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (β : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) →
      XNorm00Restr (V := Unit) θ' B Set.univ (fun ts _ => J ts) < β →
      ∃ ĥ : (Fin 3 → ℤ) → ℂ,
        (∀ᵐ t : Fin 2 → ℝ, t ∈ B → ∀ s : Fin 3 → ℝ, ![s 0, s 1] = t →
          HasSum (fun m : Fin 3 → ℤ => ĥ m * fsPhase m s) (J t)) ∧
        ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ‖ĥ m‖ₑ ≤ C * β := by
  obtain ⟨C, hC, hF⟩ := scalar_modes hθ hθθ 2
  refine ⟨C, hC, fun q B J β hc hi hJ => ?_⟩
  obtain ⟨ĥ, hae, hs⟩ := hF q B J β hc hi hJ
  refine ⟨embed2 ĥ, ?_, ?_⟩
  · filter_upwards [hae] with t ht htB s hs'
    subst hs'
    exact hasSum_embed2 ĥ s (ht htB)
  · rw [tsum_embed2]; exact hs

/-- An a.e. statement on `ℝⁿ`, pulled back along an injective choice `v` of internal times, restricted to the time domain. -/
theorem ae_clock_box {d : ℕ} {D : SumintPar.SumintDatum d} (hI : 0 < D.S.I) (tt : Fin 3 → ℝ) {n : ℕ}
    (v : Fin n → D.S.TVar) (hv : Function.Injective v) {P : (Fin n → ℝ) → Prop} (h : ∀ᵐ x : Fin n → ℝ, P x)
    {B : Set (Fin n → ℝ)} (hB : ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B)
    {Q : (D.S.TVar → ℝ) → Prop} (hQ : ∀ τ, P (fun i => τ (v i)) → (fun i => τ (v i)) ∈ B → Q τ) :
    ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), Q τ := by
  have h1 := ae_pullback_coords v hv h
  rw [ae_restrict_iff' (measurableSet_timeDom D hI _ _ _)]
  filter_upwards [h1] with τ hτ hmem
  exact hQ τ hτ (hB τ hmem)

end WaveTurbulence.VineEstS5C.P2
