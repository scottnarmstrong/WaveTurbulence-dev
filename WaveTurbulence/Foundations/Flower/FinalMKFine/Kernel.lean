/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Fine
public import WaveTurbulence.Foundations.Flower.FlFiber.Fiber
public import WaveTurbulence.Foundations.Spine.CoverFineBound
import Mathlib.Tactic

/-! # C4b FINE-PIN: the marked kernel as amplitude times the pinned time transform

- `splicedTimeIntegralMK_eq`: the pinned time integral of a decoration is `splicedFourierBMK` at its frequency.
- `ampMK`: the momentum amplitude of the marked kernel (filters and indicator times main's amplitude);
  `norm_ampMK_le_one` (filters and `ind` have modulus `≤ 1`, S Lemma 9.4).
- `splicedKernelMK_eq`: `splicedKernelMK = coupling^n · ∑' z, ampMK z · B_MK(α z)`.
- `splicedFrequency_eq_Gamma`: the frequency at an atom is an affine function of the molecular energy `Γ_v`,
  so it depends only on the labels of the darts at `v` (`splicedFrequency_congr`).
- `norm_kvec_sub_center_le`: on the support every dart momentum lies in the unit ball of its center. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ}

theorem phase_mul_eq (G : Garden w) (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (t : GBranch G.tree → ℝ) :
    phaseProd L γ δ G (cosetDecoration G L base z) t *
        ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I) =
      ∏ v : GBranch G.tree,
        Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z v * t v : ℝ) * Complex.I) := by
  simp only [phaseProd]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro v _
  rw [← Complex.exp_add]
  congr 1
  unfold splicedFrequency
  push_cast
  ring

/-- The pinned time integral is the pinned transform `B_MK` at the decoration's frequency (data without lower
bounds, ruling R187; the general form is `LBPin.splicedTimeIntegralMK_eq_LB`). -/
theorem splicedTimeIntegralMK_eq (G : Garden w) (D : SplicedKernelDataMK G d) (hlb : D.lb = fun _ => none)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedTimeIntegralMK G D L γ δ base z =
      splicedFourierBMK G D.layer D.rootTime D.fix
        (splicedFrequency G D.toSplicedKernelData L γ δ base z) := by
  rw [splicedTimeIntegralMK_lb_none G D hlb]
  unfold splicedFourierBMK
  congr 1
  funext τ
  have h : (fun t : GBranch G.tree → ℝ => phaseProd L γ δ G (cosetDecoration G L base z) t *
      ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) =
      fun t => ∏ v : GBranch G.tree, Complex.exp
        ((Real.pi * splicedFrequency G D.toSplicedKernelData L γ δ base z v * t v : ℝ) * Complex.I) := by
    funext t
    exact phase_mul_eq G D.toSplicedKernelData L γ δ base z t
  rw [h]

/-- The momentum amplitude of the marked kernel: filters and indicator times main's amplitude. -/
noncomputable def ampMK (G : Garden w) (D : SplicedKernelDataMK G d) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  D.atomW (cosetDecoration G L base z) * splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z

theorem splicedKernelMK_eq (G : Garden w) (D : SplicedKernelDataMK G d) (hlb : D.lb = fun _ => none)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernelMK G D L γ η δ base roots = (coupling d L γ δ : ℂ) ^ G.order *
      ∑' z : GenDecoration G d roots 0, ampMK G D L γ η base z.1 *
        splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) := by
  unfold splicedKernelMK
  congr 1
  apply tsum_congr
  intro z
  rw [splicedTimeIntegralMK_eq G D hlb]
  unfold ampMK splicedMomentumAmplitude
  ring

theorem mul_le_one_of {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 := by
  nlinarith

/-- Filters and the indicator have modulus at most one (S Lemma 9.4). -/
theorem norm_atomW_le_one {G : Garden w} (D : SplicedKernelDataMK G d)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (k : GNode G.tree → Mom d) : ‖D.atomW k‖ ≤ 1 := by
  unfold SplicedKernelDataMK.atomW
  rw [norm_mul, norm_prod]
  refine mul_le_one_of (prod_le_one₀ (fun _ _ => norm_nonneg _) ?_) (norm_nonneg _) ?_
  · intro a _
    rcases h : D.filt a with _ | q
    · simp
    · simpa using hfilt a q h _
  · rw [Complex.norm_real, Real.norm_of_nonneg (hind k).1]
    exact (hind k).2

theorem norm_ampMK_le_one {G : Garden w} (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ‖ampMK G D L γ η base z‖ ≤ 1 := by
  unfold ampMK
  rw [norm_mul]
  exact mul_le_one_of (norm_atomW_le_one D hfilt hind _) (norm_nonneg _)
    (norm_splicedMomentumAmplitude_le_one G _ hD L γ η base z)

theorem enorm_ampMK_le_one {G : Garden w} (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ‖ampMK G D L γ η base z‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  simpa only [ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (norm_ampMK_le_one D hD hfilt hind L γ η base z)

theorem amp_ne_zero_of_ampMK {G : Garden w} {D : SplicedKernelDataMK G d} {L γ η : ℝ} {base : Mom d}
    {z : GNode G.tree → (Fin d → ℤ)} (h : ampMK G D L γ η base z ≠ 0) :
    splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z ≠ 0 :=
  right_ne_zero_of_mul h

/-- The frequency at an atom is an affine function of the molecular energy `Γ_v` (σ = 0 in main's residual). -/
theorem splicedFrequency_eq_Gamma (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelData G d) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (γ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (v : GBranch G.tree) :
    splicedFrequency G D L γ δ base z.1 v =
      -((G.molecule.Gamma L base (bondIndex G z.1) v - splicedEnergyCenter G hp D L γ δ base roots 0 v) *
        (δ * L ^ (2 * γ))) := by
  have h := spliced_energy_residual G hp D hL hδ γ base roots 0 z v
  simp only [Pi.zero_apply, Int.cast_zero, zero_sub] at h
  linarith

/-- `Γ_v` reads only the labels of the darts at `v`. -/
theorem Gamma_congr {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (L : ℝ) (base : Mom d) {κ κ' : D → (Fin d → ℤ)} (v : V) (h : ∀ x ∈ M.dartsAt v, κ x = κ' x) :
    M.Gamma L base κ v = M.Gamma L base κ' v := by
  unfold Molecule.Gamma
  apply sum_congr rfl
  intro x hx
  simp only [Molecule.kvec, h x hx]

/-- On the support, the momentum of every dart lies in the unit ball of its center. -/
theorem norm_kvec_sub_center_le (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0) (x : GardenDart G) :
    ‖latticePoint L (bondIndex G z.1 x) - (D.center x - base)‖ ≤ 1 := by
  have hballs := (splicedMomentumAmplitude_support G D hD L γ η base z.1 hz).2.2
  have hdec := spliced_molecule_decoration G hp hL base roots z
  have e : ∀ y, latticePoint L (bondIndex G z.1 y) - (D.center y - base) =
      base + latticePoint L (bondIndex G z.1 y) - D.center y := fun y => by abel
  rw [e]
  by_cases hx : G.molecule.out x = true
  · have hm : x ∈ G.molecule.bonds := by
      simp only [Molecule.bonds, mem_filter, Finset.mem_univ, true_and]; exact hx
    exact hballs x hm
  · have hx' : G.molecule.out x = false := Bool.eq_false_iff.mpr hx
    have hm : G.molecule.mate x ∈ G.molecule.bonds := by
      simp only [Molecule.bonds, mem_filter, Finset.mem_univ, true_and, G.molecule.out_mate, hx',
        Bool.not_false]
    have hh := hballs (G.molecule.mate x) hm
    rwa [hdec.1 x, hD.1 x] at hh

end WaveTurbulence.Flower.FinalMKFine
