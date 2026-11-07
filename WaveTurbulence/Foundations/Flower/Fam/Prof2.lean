/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Bounds
public import WaveTurbulence.Foundations.Flower.Polar.Main
public import WaveTurbulence.Foundations.XChain.ProductCut.ProdCut
/-! # FL-FAM: the high-weight profile bound, support of the family profile at the frontier radii,
and the closure of the support predicate under the polarization perturbation. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Set WaveTurbulence.Flower.Typed

theorem profile_high {Pm : ℕ} (P : WTParams) (hd : 3 ≤ P.d) (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (htime : P.τstar = (P.D : ℝ) * P.δ) (hsol : ContinuousOn P.φ (Icc 0 P.τstar))
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (N : ℕ) (M A : ℝ) (tail : Fin (2 * Pm) → Bool) (z : Fin (2 * Pm) → ℝ)
    (hM : Mgen P.d (Wt P p) ≤ M) (hA : A = M / (4 * ((2 * N + 1 : ℕ) : ℝ))) (hA1 : 1 ≤ A)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) (FC23.extractionRadius (40 * P.d) N (Cfam P.d) (Ufam P p) M)) :
    ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d + 4 * P.Lambda (p + 1))
      (familyProfile (inputsF P R) p M A tail z q j j') ≤ ENNReal.ofReal (hiB P p) := by
  intro q hq j j'
  have hd1 : 1 ≤ P.d := by omega
  have hlam := weights_le P hd hp
  have hS : 40 * P.d ≤ Wt P p := by unfold Wt; omega
  have h0 := inputs_bound P hd1 hL hδ htime hsol hp R hR (A := 40 * P.d) (B := Wt P p)
    (by have := LGSpine.forty_dim_le_Lambda P hd1 hp.le; exact this) (by omega) q hq
  have h1 := inputs_bound P hd1 hL hδ htime hsol hp R hR (A := 40 * P.d) (B := 3 * Wt P p)
    (by have := LGSpine.forty_dim_le_Lambda P hd1 hp.le; exact this) hlam.1 q hq
  have := profile_bound hd1 (Wt P p) hS (inputsF P R) p N (Ufam P p) M A (Ufam P p) (Ufam P p) tail z q j j'
    (by linarith [Ufam_one P p]) (by linarith [Ufam_one P p]) (Ufam_one P p) le_rfl hM hA hA1 hz h0 h1
  exact this.trans (ENNReal.ofReal_le_ofReal (le_trans (by linarith) (le_max_left _ _)))

/-- The frontier radius of tree `j` for the family weight. -/
def rad {w : ℕ} (tail small : Fin w → Bool) (M : ℝ) (j : Fin w) : ℝ :=
  if tail j && small j then M / 2 else M

theorem endpoint_top_tail_zero (p : ℕ) {M A z r : ℝ} (hM : 0 < M) (hr : M / 2 ≤ r) :
    FC23.endpointFactor p p true M A z r = 0 := by
  have h1 : chi0 (r / (M / 2)) = 0 := by
    rw [FC23.frozen_chi0_eq]
    apply Fourier.chi0_eq_zero
    rw [abs_of_nonneg (div_nonneg ((by positivity : (0:ℝ) ≤ M / 2).trans hr) (by positivity))]
    rw [one_le_div (by positivity)]
    exact hr
  unfold FC23.endpointFactor
  simp [h1]

theorem profile_support_rad {w d : ℕ} (F : ℕ → Mom d → ℝ) (p : ℕ) (M A : ℝ) (tail small : Fin w → Bool)
    (z : Fin w → ℝ) (hM : 0 < M) (j j' : Fin w) (x : Mom d) (hx : rad tail small M j ≤ ‖x‖) :
    familyProfile F p M A tail z p j j' x = 0 ∧ familyProfile F p M A tail z p j' j x = 0 := by
  unfold rad at hx
  by_cases hc : (tail j && small j) = true
  · rw [if_pos hc] at hx
    have ht : tail j = true := by simpa using (Bool.and_eq_true_iff.mp hc).1
    have h0 := endpoint_top_tail_zero p (A := A) (z := z j) hM (r := ‖x‖) hx
    constructor
    · unfold familyProfile; rw [ht] at *; simp [h0]
    · unfold familyProfile; rw [ht] at *; simp [h0]
  · rw [if_neg hc] at hx
    exact ⟨familyProfile_support F p M A tail z j j' x hM hx, familyProfile_support F p M A tail z j' j x hM hx⟩

/-- The support predicate at radii `ρ`. -/
def SuppAt {d w : ℕ} (p : ℕ) (ρ : Fin w → ℝ) (g : ℕ → Fin w → Fin w → Mom d → ℝ) : Prop :=
  ∀ j j' x, ρ j ≤ ‖x‖ → g p j j' x = 0 ∧ g p j' j x = 0

theorem SuppAt.perturb {d w : ℕ} {p : ℕ} {ρ : Fin w → ℝ} {g : ℕ → Fin w → Fin w → Mom d → ℝ}
    (hg : SuppAt p ρ g) (σ : ℝ) (j₀ : Fin w) (i : Fin d) (μ : ℝ) :
    SuppAt p ρ (LGSpine.TProf.perturb g (Polar.polForm σ j₀ i g) μ) := by
  intro j j' x hx
  obtain ⟨h1, h2⟩ := hg j j' x hx
  simp [LGSpine.TProf.perturb, Polar.polForm, h1, h2]

theorem abs_frontierW_le {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (Rf : Fin w → Option ℝ)
    (k : GNode LG.garden.tree → Mom d) : |frontierW LG p Rf k| ≤ 1 := by
  unfold frontierW
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun a _ => ?_
  split_ifs
  · cases Rf a.1.1 with
    | none => simp
    | some r =>
      simp only [Option.elim]
      rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
      exact XChain.ProductCut.chi0_le_one _
  · simp

end WaveTurbulence.Flower.Fam
