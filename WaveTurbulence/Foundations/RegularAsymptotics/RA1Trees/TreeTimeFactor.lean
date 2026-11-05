/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimePolynomialProfile
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-! # The geometric bound for the literal source tree time factor -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- The source polynomial has a geometric weighted envelope, independent of order cutoffs. -/
theorem exists_tree_time_envelope_mass : ∃ K D : ℝ, 0 ≤ K ∧ 1 ≤ D ∧
    ∀ (X : RegChain) (n : ℕ), X.size = 2*n → ∀ θ : ℝ, θ ≤ 1 →
      (∫⁻ lam : ℝ × ℝ, wL θ lam * treeTimePolynomialEnvelope (treeTimePolynomial X) lam) ≤
        ENNReal.ofReal (K * D^n) := by
  obtain ⟨K,B,hK,hB,hb⟩ := exists_tree_tensor_profile_mass
  let D := 4 * max 1 B
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [le_max_left (1:ℝ) B]
  refine ⟨K,D,hK,hD,?_⟩
  intro X n hn θ hθ
  have hd : chainTimeDegree X ≤ n := by have := twice_chainTimeDegree_le_size X; omega
  apply (treeTimePolynomialEnvelope_mass hK hB hb (treeTimePolynomial X)
    (chainTimeDegree X) (treeTimePolynomial_degree X) θ hθ).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ K * B^chainTimeDegree X * (4:ℝ)^chainTimeDegree X :=
      mul_le_mul_of_nonneg_left (treeTimePolynomialMass_le X) (mul_nonneg hK (pow_nonneg hB _))
    _ = K * (4*B)^chainTimeDegree X := by rw [mul_pow]; ring
    _ ≤ K * D^chainTimeDegree X := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by dsimp only [D]; linarith only [le_max_right (1:ℝ) B]) _) hK
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hd) hK

/-- The literal JBtree time factor has its required uniform geometric norm bound.
The constant is chosen before every tree, order and order-cutoff exponent. -/
theorem exists_tree_JB_time_bound {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : RegChain) (n : ℕ), X.size = 2*n →
      ∀ T : Set (Fin 2 → ℝ),
      (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      (∀ t ∈ T, t 1 ≤ t 0) →
      XNorm00Restr (V := Unit) (1-η) T Set.univ
        (fun ts _ => (X.JBtree 0 (ts 0) (ts 1):ℂ)) ≤ ENNReal.ofReal (C*C^n) := by
  obtain ⟨K,D,hK,hD,hbound⟩ := exists_tree_time_envelope_mass
  let H : ℝ≥0∞ := ENNReal.ofReal (2^(1-η))*Fourier.timeFourierNorm (1-η) unitSquareCutoff
  have hH : H < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (timeFourierNorm_unitSquareCutoff_lt_top _)
  let C := max 1 (H.toReal*K+D)
  have hC : 1 ≤ C := le_max_left _ _
  have hfront : H.toReal*K ≤ C :=
    (le_add_of_nonneg_right (zero_le_one.trans hD)).trans (le_max_right _ _)
  have hbase : D ≤ C :=
    (le_add_of_nonneg_left (mul_nonneg ENNReal.toReal_nonneg hK)).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro X n hn T hT htriangle
  let P := treeTimePolynomialProfile (treeTimePolynomial X)
  let E := treeTimePolynomialEnvelope (treeTimePolynomial X)
  have hEq : (fun ts : T => fun _ : (Set.univ : Set Unit) =>
      (X.JBtree 0 ((ts:Fin 2 → ℝ) 0) ((ts:Fin 2 → ℝ) 1):ℂ)) =
      (fun ts : T => fun _ : (Set.univ : Set Unit) => pairedInverseProfile P ts) := by
    funext ts _
    unfold pairedInverseProfile
    rw [integral_treeTimePolynomialProfile _ (hT ts ts.property 0) (hT ts ts.property 1)]
    rw [tree_JB_eq_treeTimePolynomial X _ _ (hT ts ts.property 1).1 (htriangle ts ts.property)]
    have hcast (zs : List TreeTimeTerm) :
        (((zs.map (fun z => z.eval ((ts:Fin 2 → ℝ) 0) ((ts:Fin 2 → ℝ) 1))).sum:ℝ):ℂ) =
          (zs.map (fun z => (z.eval ((ts:Fin 2 → ℝ) 0) ((ts:Fin 2 → ℝ) 1):ℂ))).sum := by
      induction zs with
      | nil => simp
      | cons z zs ih => simp only [List.map_cons, List.sum_cons, Complex.ofReal_add, ih]
    exact hcast _
  rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00, hEq]
  apply (mixedRestrictionNorm00_pairedProfile_le (by linarith : 0 ≤ 1-η) hT Set.univ
    (A := fun lam (_ : Unit) => P lam) (fun _ => integrable_treeTimePolynomialProfile _)
    (measurable_treeTimePolynomialEnvelope _) (fun _ => ae_of_all _ (enorm_treeTimePolynomialProfile_le _))).trans
  change H * (∫⁻ lam, wL (1-η) lam * E lam) ≤ _
  apply (mul_le_mul' le_rfl (hbound X n hn (1-η) (by linarith))).trans
  rw [← ENNReal.ofReal_toReal hH.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (H.toReal*K)*D^n := by ring
    _ ≤ C*C^n := mul_le_mul hfront
      (pow_le_pow_left₀ (zero_le_one.trans hD) hbase n) (by positivity) (zero_le_one.trans hC)

end WaveTurbulence.RegAsymp
