/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Lead
public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeGate
public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleGate

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`: leading terms as separated sums (PL23-30D)

* `treeMz`, `tree_eq_sum`: `𝒜_𝒯(t,s,k) = ∑_Z M_Z(k) 𝒥ℬ*_𝒯(t,s)` with `M_Z = coef · w_Z · N*_Z`;
* `coupleMz`, `couple_eq_sum`: the same for couples;
* `SNorm_sum_const_mul_le`: a sum of constant multiples in `𝔖^{Λ,Λ₂}`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.NormBridgeScratch

variable {d : ℕ}

/-- The coefficient of the leading term of a tree code. -/
noncomputable def treeCoef (δ : ℝ) (X : RegChain) (ζ : ℤˣ) : ℂ :=
  (2 : ℂ)⁻¹ ^ X.size * (δ : ℂ) ^ (X.size / 2) * zetaOfTrees ![ζ] ![X.plug ζ .leaf]

noncomputable def treeMz (δ : ℝ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (Z : Finset (Fin 1 × Path))
    (k : Mom d) : ℂ :=
  treeCoef δ X ζ * specialWeight ![ζ] Z * (LeafApp.chainNstar H Z X ζ (0, []) k : ℂ)

theorem norm_treeCoef_le {δ : ℝ} (hδ : 0 ≤ δ) {X : RegChain} (ζ : ℤˣ) {n : ℕ} (hsize : X.size = 2 * n) :
    ‖treeCoef δ X ζ‖ ≤ δ ^ n := by
  unfold treeCoef
  rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hδ, hsize, Nat.mul_div_cancel_left n two_pos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h1 : (2⁻¹ : ℝ) ^ (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc (2⁻¹ : ℝ) ^ (2 * n) * δ ^ n ≤ 1 * δ ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg hδ n)
    _ = δ ^ n := one_mul _

theorem tree_eq_sum {δ r : ℝ} (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (hdom : X.dominant = true)
    (t s : ℝ) (k : Mom d) :
    LeafApp.tree δ r H X ζ t s k =
      ∑ Z ∈ specialSets (X.treeLinks ζ), treeMz δ H X ζ Z k * (X.JBtree r t s : ℂ) := by
  unfold LeafApp.tree
  rw [ite_eq_left hdom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  unfold treeMz treeCoef
  ring

theorem tree_eq_zero {δ r : ℝ} (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (hdom : ¬ X.dominant = true)
    (t s : ℝ) (k : Mom d) : LeafApp.tree δ r H X ζ t s k = 0 := by
  unfold LeafApp.tree
  rw [ite_eq_right hdom]

theorem SNorm_treeMz_le {δ : ℝ} (hδ : 0 ≤ δ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) {n : ℕ}
    (hsize : X.size = 2 * n) {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) {cM : ℝ} (hcM : 0 ≤ cM) (Z : Finset (Fin 1 × Path))
    (hZ : Z ∈ specialSets (X.treeLinks ζ))
    (hM : SNormR Λ Λ₂ (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM) :
    SNorm Λ Λ₂ (fun k => treeMz δ H X ζ Z k) ≤ ENNReal.ofReal (δ ^ n * cM) := by
  have h := SNorm_const_mul_bound hΛ (treeCoef δ X ζ * specialWeight ![ζ] Z)
    (fun k => (LeafApp.chainNstar H Z X ζ (0, []) k : ℂ)) (C := cM) hM
  have hw := norm_specialWeight_le ![ζ] Z
  have hc := norm_treeCoef_le hδ ζ hsize (X := X)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [norm_mul]
  calc ‖treeCoef δ X ζ‖ * ‖specialWeight ![ζ] Z‖ * cM ≤ δ ^ n * 1 * cM := by
        gcongr
    _ = δ ^ n * cM := by ring

/-- The coefficient of the leading term of a couple code. -/
noncomputable def coupleCoef (δ : ℝ) (Q : RegCpl) : ℂ :=
  (2 : ℂ)⁻¹ ^ Q.size * (δ : ℂ) ^ (Q.size / 2) * zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2]

noncomputable def coupleMz (δ : ℝ) (H : LeafProfiles 2 d) (Q : RegCpl) (Z : Finset (Fin 2 × Path))
    (k : Mom d) : ℂ :=
  coupleCoef δ Q * specialWeight ![1, -1] Z * (LeafApp.cplMstar H Z Q (0, []) (1, []) k : ℂ)

theorem norm_coupleCoef_le {δ : ℝ} (hδ : 0 ≤ δ) {Q : RegCpl} {n : ℕ} (hsize : Q.size = 2 * n) :
    ‖coupleCoef δ Q‖ ≤ δ ^ n := by
  unfold coupleCoef
  rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hδ, hsize, Nat.mul_div_cancel_left n two_pos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h1 : (2⁻¹ : ℝ) ^ (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc (2⁻¹ : ℝ) ^ (2 * n) * δ ^ n ≤ 1 * δ ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg hδ n)
    _ = δ ^ n := one_mul _

theorem couple_eq_sum {δ r : ℝ} (H : LeafProfiles 2 d) (Q : RegCpl) (hdom : Q.dominant = true)
    (t s : ℝ) (k : Mom d) :
    LeafApp.couple δ r H Q t s k =
      ∑ Z ∈ specialSets Q.links, coupleMz δ H Q Z k * (Q.JB r t s : ℂ) := by
  unfold LeafApp.couple
  rw [ite_eq_left hdom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  unfold coupleMz coupleCoef
  ring

theorem couple_eq_zero {δ r : ℝ} (H : LeafProfiles 2 d) (Q : RegCpl) (hdom : ¬ Q.dominant = true)
    (t s : ℝ) (k : Mom d) : LeafApp.couple δ r H Q t s k = 0 := by
  unfold LeafApp.couple
  rw [ite_eq_right hdom]

theorem SNorm_coupleMz_le {δ : ℝ} (hδ : 0 ≤ δ) (H : LeafProfiles 2 d) (Q : RegCpl) {n : ℕ}
    (hsize : Q.size = 2 * n) {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) {cM : ℝ} (hcM : 0 ≤ cM) (Z : Finset (Fin 2 × Path))
    (hM : SNormR Λ Λ₂ (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM) :
    SNorm Λ Λ₂ (fun k => coupleMz δ H Q Z k) ≤ ENNReal.ofReal (δ ^ n * cM) := by
  have h := SNorm_const_mul_bound hΛ (coupleCoef δ Q * specialWeight ![1, -1] Z)
    (fun k => (LeafApp.cplMstar H Z Q (0, []) (1, []) k : ℂ)) (C := cM) hM
  have hw := norm_specialWeight_le ![1, -1] Z
  have hc := norm_coupleCoef_le hδ hsize (Q := Q)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [norm_mul]
  calc ‖coupleCoef δ Q‖ * ‖specialWeight ![1, -1] Z‖ * cM ≤ δ ^ n * 1 * cM := by
        gcongr
    _ = δ ^ n * cM := by ring

end WaveTurbulence.PL2330
