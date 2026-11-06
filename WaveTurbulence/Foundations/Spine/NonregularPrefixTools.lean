/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LayergardenAssembly
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.Spine.StageOrderGrowth
public import WaveTurbulence.Foundations.Spine.SchwartzUniformNorm
/-! Tools for the late choice of `L` in the parameter prefix. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter

/-- Context facts of the prefix (the WKE solution, `tau* = D delta`, `D >= 1`, `phi_in >= 0`) as part of the
predicate. -/
@[expose] def WKEContext (P : WTParams) : Prop :=
  IsWKESolution P.φin P.τstar P.φ ∧ P.τstar = (P.D : ℝ) * P.δ ∧ 1 ≤ P.D ∧ ∀ k, 0 ≤ P.φin k

theorem prefix_with_wke_context {Q : WTParams → Prop} (hQ : WTPrefix Q) :
    WTPrefix (fun P => Q P ∧ WKEContext P) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  exact ⟨hQ L hL, hsol, htime, hD, hφin⟩

theorem wkeContext_largeConstantMonotone : LargeConstantMonotone WKEContext :=
  fun _ _ _ _ _ _ _ _ _ h => h

/-- Late choice of `L`: if the property holds eventually in `L` for every parameter record whose prefix
predicate holds for all larger `L`, it holds in the prefix. -/
theorem prefix_late {Q S : WTParams → Prop} (hQ : WTPrefix Q)
    (hS : ∀ P : WTParams, (∀ L : ℝ, P.L ≤ L → Q {P with L := L}) →
      ∀ᶠ L : ℝ in atTop, S {P with L := L}) : WTPrefix S := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ hδ D hD htime
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    (hS ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L₀⟩ (fun L hL => hQ L hL))
  exact ⟨C₂, hC₂, max L₀ L₁, hL₀.trans (le_max_left _ _),
    fun L hL => hL₁ L ((le_max_right _ _).trans hL)⟩

theorem one_le_Rdown (P : WTParams) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d) (k : ℕ) :
    1 ≤ P.Rdown k := by
  induction k with
  | zero =>
    unfold WTParams.Rdown
    apply Nat.le_floor
    simpa using one_le_pow₀ hlog
  | succ k ih =>
    unfold WTParams.Rdown
    exact Nat.one_le_pow _ _ (Nat.one_le_pow _ _ ih)

theorem one_le_R (P : WTParams) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d) (p : ℕ) : 1 ≤ P.R p :=
  one_le_Rdown P hlog hd _

theorem theta_le_two (P : WTParams) (hη : 0 ≤ P.η) (q : ℕ) : P.theta q ≤ 2 * P.η ^ 20 := by
  unfold WTParams.theta
  have h : ((2 : ℝ)⁻¹) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have : 0 ≤ P.η ^ 20 := pow_nonneg hη 20
  nlinarith

theorem eta_gap_pos {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) : 2 * η ^ 20 < η ^ 7 := by
  have h7 : 0 < η ^ 7 := pow_pos hη 7
  have h13 : η ^ 13 ≤ (1 / 8) ^ 13 := pow_le_pow_left₀ hη.le hη8 13
  have h20 : η ^ 20 = η ^ 7 * η ^ 13 := by rw [← pow_add]
  have : (1 / 8 : ℝ) ^ 13 ≤ 1 / 4 := by norm_num
  rw [h20]
  nlinarith

end WaveTurbulence.LGSpine
