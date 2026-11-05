/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimePolynomialBudget
public import WaveTurbulence.Foundations.RegAsymp.TreeTensorProfile
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction

/-! # Exact Fourier profiles of the literal finite source time polynomials -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

def TreeTimeTerm.profile (z : TreeTimeTerm) (lam : ℝ × ℝ) : ℂ :=
  (z.coeff:ℂ) * (treeTimeMonomialProfile z.upperPower lam.1 *
    treeTimeMonomialProfile z.lowerPower lam.2)

def treeTimePolynomialProfile (zs : List TreeTimeTerm) (lam : ℝ × ℝ) : ℂ :=
  (zs.map (fun z => z.profile lam)).sum

def treeTimePolynomialEnvelope (zs : List TreeTimeTerm) (lam : ℝ × ℝ) : ℝ≥0∞ :=
  (zs.map (fun z => ‖z.profile lam‖ₑ)).sum

theorem TreeTimeTerm.integrable_profile (z : TreeTimeTerm) : Integrable z.profile :=
  ((integrable_treeTimeMonomialProfile z.upperPower).mul_prod
    (integrable_treeTimeMonomialProfile z.lowerPower)).const_mul _

theorem TreeTimeTerm.continuous_profile (z : TreeTimeTerm) : Continuous z.profile := by
  unfold TreeTimeTerm.profile treeTimeMonomialProfile
  exact continuous_const.mul
    (((contDiff_ftπ (contDiff_treeTimeMonomial z.upperPower)
      (hasCompactSupport_treeTimeMonomial z.upperPower)).continuous.comp continuous_fst).mul
      ((contDiff_ftπ (contDiff_treeTimeMonomial z.lowerPower)
        (hasCompactSupport_treeTimeMonomial z.lowerPower)).continuous.comp continuous_snd))

theorem integrable_treeTimePolynomialProfile (zs : List TreeTimeTerm) :
    Integrable (treeTimePolynomialProfile zs) := by
  induction zs with
  | nil =>
    change Integrable (fun _ : ℝ × ℝ => (0:ℂ))
    exact MeasureTheory.integrable_zero (ℝ × ℝ) ℂ volume
  | cons z zs ih => exact z.integrable_profile.add ih

theorem measurable_treeTimePolynomialEnvelope (zs : List TreeTimeTerm) :
    Measurable (treeTimePolynomialEnvelope zs) := by
  induction zs with
  | nil => exact measurable_const
  | cons z zs ih =>
    change Measurable (fun lam : ℝ × ℝ => ‖z.profile lam‖ₑ + treeTimePolynomialEnvelope zs lam)
    exact z.continuous_profile.measurable.enorm.add ih

theorem enorm_treeTimePolynomialProfile_le (zs : List TreeTimeTerm) (lam : ℝ × ℝ) :
    ‖treeTimePolynomialProfile zs lam‖ₑ ≤ treeTimePolynomialEnvelope zs lam := by
  induction zs with
  | nil => simp [treeTimePolynomialProfile, treeTimePolynomialEnvelope]
  | cons z zs ih =>
    exact (enorm_add_le (z.profile lam) (treeTimePolynomialProfile zs lam)).trans
      (add_le_add le_rfl ih)

theorem TreeTimeTerm.integral_profile (z : TreeTimeTerm) {t s : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    (∫ lam : ℝ × ℝ, z.profile lam * e2 lam t s) = (z.eval t s:ℂ) := by
  unfold TreeTimeTerm.profile TreeTimeTerm.eval
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have hi := integral_treeTimeMonomialProfile_on_square z.upperPower z.lowerPower ht hs
  simp_rw [mul_assoc] at hi
  rw [hi]
  push_cast
  ring

theorem TreeTimeTerm.integrable_profile_e2 (z : TreeTimeTerm) (t s : ℝ) :
    Integrable (fun lam => z.profile lam * e2 lam t s) := by
  exact z.integrable_profile.mul_bdd (by
      have h : Continuous (fun lam : ℝ × ℝ => e2 lam t s) := by unfold e2; fun_prop
      exact h.aestronglyMeasurable)
    (ae_of_all _ (fun lam => le_of_eq (norm_e2 lam t s)))

theorem integral_treeTimePolynomialProfile (zs : List TreeTimeTerm) {t s : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    (∫ lam : ℝ × ℝ, treeTimePolynomialProfile zs lam * e2 lam t s) =
      ((zs.map (fun z => z.eval t s)).sum:ℂ) := by
  induction zs with
  | nil => simp [treeTimePolynomialProfile]
  | cons z zs ih =>
    have hrest : Integrable (fun lam => treeTimePolynomialProfile zs lam * e2 lam t s) :=
      (integrable_treeTimePolynomialProfile zs).mul_bdd
        (by
      have h : Continuous (fun lam : ℝ × ℝ => e2 lam t s) := by unfold e2; fun_prop
      exact h.aestronglyMeasurable)
        (ae_of_all _ (fun lam => le_of_eq (norm_e2 lam t s)))
    simp only [treeTimePolynomialProfile, List.map_cons, List.sum_cons, add_mul]
    change (∫ lam, z.profile lam * e2 lam t s + treeTimePolynomialProfile zs lam * e2 lam t s) = _
    rw [integral_add (z.integrable_profile_e2 t s) hrest, z.integral_profile ht hs, ih]

/-- Homogeneous source polynomial coefficient mass controls its full weighted profile. -/
theorem treeTimePolynomialEnvelope_mass {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hb : ∀ a b θ, θ ≤ 1 →
      (∫⁻ lam : ℝ × ℝ, wL θ lam *
        ‖treeTimeMonomialProfile a lam.1 * treeTimeMonomialProfile b lam.2‖ₑ) ≤
        ENNReal.ofReal (K * B^(a+b)))
    (zs : List TreeTimeTerm) (p : ℕ) (hdeg : ∀ z ∈ zs, z.upperPower+z.lowerPower=p)
    (θ : ℝ) (hθ : θ ≤ 1) :
    (∫⁻ lam : ℝ × ℝ, wL θ lam * treeTimePolynomialEnvelope zs lam) ≤
      ENNReal.ofReal (K * B^p * treeTimePolynomialMass zs) := by
  induction zs with
  | nil => simp [treeTimePolynomialEnvelope, treeTimePolynomialMass]
  | cons z zs ih =>
    have hd := hdeg z (List.mem_cons_self)
    have hds : ∀ q ∈ zs, q.upperPower+q.lowerPower=p :=
      fun q hq => hdeg q (List.mem_cons_of_mem _ hq)
    have hm : Measurable (fun lam : ℝ × ℝ => wL θ lam * ‖z.profile lam‖ₑ) :=
      (measurable_wL θ).mul z.continuous_profile.measurable.enorm
    have hz : (∫⁻ lam : ℝ × ℝ, wL θ lam * ‖z.profile lam‖ₑ) ≤
        ENNReal.ofReal (K * B^p * ‖z.coeff‖) := by
      have he : (fun lam : ℝ × ℝ => wL θ lam * ‖z.profile lam‖ₑ) =
          fun lam => ENNReal.ofReal ‖z.coeff‖ * (wL θ lam *
            ‖treeTimeMonomialProfile z.upperPower lam.1 *
              treeTimeMonomialProfile z.lowerPower lam.2‖ₑ) := by
        funext lam
        have hc : ‖(z.coeff:ℂ)‖ₑ = ENNReal.ofReal ‖z.coeff‖ := by
          rw [← ofReal_norm, Complex.norm_real]
        simp only [TreeTimeTerm.profile, enorm_mul, hc]
        ring
      rw [he, lintegral_const_mul _ (by
        exact (measurable_wL θ).mul
          ((contDiff_ftπ (contDiff_treeTimeMonomial z.upperPower)
            (hasCompactSupport_treeTimeMonomial z.upperPower)).continuous.measurable.comp measurable_fst |>.mul
          ((contDiff_ftπ (contDiff_treeTimeMonomial z.lowerPower)
            (hasCompactSupport_treeTimeMonomial z.lowerPower)).continuous.measurable.comp measurable_snd) |>.enorm))]
      apply (mul_le_mul' le_rfl (hb z.upperPower z.lowerPower θ hθ)).trans
      rw [hd, ← ENNReal.ofReal_mul (norm_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact le_of_eq (mul_comm _ _)
    change (∫⁻ lam : ℝ × ℝ, wL θ lam * (‖z.profile lam‖ₑ + treeTimePolynomialEnvelope zs lam)) ≤ _
    simp_rw [mul_add]
    rw [lintegral_add_left hm]
    apply (add_le_add hz (ih hds)).trans
    rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hK (pow_nonneg hB _)) (norm_nonneg _))
      (mul_nonneg (mul_nonneg hK (pow_nonneg hB _)) (treeTimePolynomialMass_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    simp only [treeTimePolynomialMass, List.map_cons, List.sum_cons]
    exact le_of_eq (mul_add _ _ _).symm

end WaveTurbulence.RegAsymp
