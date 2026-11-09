/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone1
/-! **L6E2, part 2: the cone label counts at an Operation-1 removal** (Theorem 6.1 (e) at Op 1; Lemma 5.2).

L6-STEP1's Step-1 label counts with the joint gap in the creation cone: the count constant is multiplied by
`coneX d L η = 3·5^{d-1} θ₀^{d-1}` (`θ₀ = L^{-6η}`). L6-STEP1's counts are used as black boxes on the pieces of the
split by the joint gap (`Op1Cone1`).
* `vine_count_cone` (single vine; from `Step1.vine_count_main`), `hyper_count_cone` (hyper object; from
  `Step1.hyper_count_main`): `Step1.VineCountInput' K L γ δ ρ (Cf · coneX d L η) C₂ w Adm P 4`;
* `double_count_cone` (two double bonds; from `Step1.DoubleShape.labelSet_le_vineG`):
  `Step1.VineCountInputDouble K L γ δ R ρ ((9^d·5^d·2d) · coneX d L η) w Adm 0`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {d : ℕ}

/-- `vineF'` at `ρ = L⁻¹`, times a count `N ≤ X (ρL)^d`, is `vineF'` at `ρ` with the constant `Cf · X`. -/
theorem vineF'_split {L γ δ ρ Cf C₂ Λ X N : ℝ} (m e : ℕ) (hL : 1 ≤ L) (hδ : 0 < δ) (hCf : 0 ≤ Cf) (hC₂ : 0 ≤ C₂)
    (hΛ : 0 < Λ) (hN : N ≤ X * (ρ * L) ^ d) :
    N * VineCount.vineF' d L γ δ L⁻¹ Cf C₂ Λ m e ≤ VineCount.vineF' d L γ δ ρ (Cf * X) C₂ Λ m e := by
  have hL0 : 0 < L := by linarith
  set Y : ℝ := Cf * C₂ ^ m * L ^ d * L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) * δ ^ (-(m : ℝ) / 2) *
    Real.log L ^ e / Λ with hY
  have hY0 : 0 ≤ Y := by
    have := Real.log_nonneg hL
    rw [hY]; positivity
  have e1 : VineCount.vineF' d L γ δ L⁻¹ Cf C₂ Λ m e = Y := by
    unfold VineCount.vineF'; rw [inv_mul_cancel₀ hL0.ne', one_pow, hY]; ring
  have e2 : VineCount.vineF' d L γ δ ρ (Cf * X) C₂ Λ m e = (X * (ρ * L) ^ d) * Y := by
    unfold VineCount.vineF'; rw [hY]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hN hY0

/-- `vineG` at `ρ = L⁻¹`, times a count `N ≤ X (ρL)^d`, is `vineG` at `ρ` with the constant `Cf · X` (`R > 0`). -/
theorem vineG_split {L γ δ R ρ Cf X N : ℝ} (e : ℕ) (hL : 1 ≤ L) (hδ : 0 < δ) (hR : 0 < R) (hCf : 0 ≤ Cf)
    (hN : N ≤ X * (ρ * L) ^ d) :
    N * vineG d L γ δ R L⁻¹ Cf e ≤ vineG d L γ δ R ρ (Cf * X) e := by
  have hL0 : 0 < L := by linarith
  have hmin : 0 ≤ min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) := by
    have h1 : 0 ≤ R⁻¹ * L ^ ((d : ℝ) - 2 * γ) := by positivity
    have h2 : (0 : ℝ) ≤ L ^ d := by positivity
    exact le_min h1 h2
  set Y : ℝ := Cf * L ^ d * (L ^ (d - 1) + δ⁻¹ * min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d)) * Real.log L ^ e
    with hY
  have hY0 : 0 ≤ Y := by
    have hlog := Real.log_nonneg hL
    rw [hY]; positivity
  have e1 : vineG d L γ δ R L⁻¹ Cf e = Y := by
    unfold vineG; rw [inv_mul_cancel₀ hL0.ne', one_pow, hY]; ring
  have e2 : vineG d L γ δ R ρ (Cf * X) e = (X * (ρ * L) ^ d) * Y := by
    unfold vineG; rw [hY]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hN hY0

/-- The black-box step: if every piece of the split has at most `B` labels and the joint gaps lie in `coneSet`, the
class has at most `#coneSet · B` labels, and `#coneSet ≤ coneX d L η · (ρL)^d`. -/
theorem labelSet_cone_le {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : Step1.VineCut g M) (L γ δ η ρ : ℝ) (hL : 0 < L) (hd : 1 ≤ d) (hρL : 1 ≤ ρ * L)
    (hθρ : 1 ≤ L ^ (-6 * η) * (ρ * L)) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ ρ) (hcone : JointCone K L γ δ η w Adm)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (hP : ParamOK M c k0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ r : Fin d → ℤ, ((K.labelSet L γ δ w (AdmFix K Adm r) c β k0).encard : ℝ≥0∞) ≤ ENNReal.ofReal B)
    (F : ℝ) (hF : coneX d L η * (ρ * L) ^ d * B ≤ F) :
    ((K.labelSet L γ δ w Adm c β k0).encard : ℝ≥0∞) ≤ ENNReal.ofReal F := by
  obtain ⟨ctr, hctr, hc⟩ := hcone c β k0 hP
  have hsplit := labelSet_le_split K L γ δ w Adm c β k0 (coneSet d L ρ (L ^ (-6 * η)) ctr)
    (rint_mem_coneSet K L hL w Adm γ δ η ρ c β k0 ctr hgap hc) _ (fun r _ => hB r)
  refine hsplit.trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ hF)
  have hcard := card_coneSet_le_rho L ρ (L ^ (-6 * η)) hL hρL hθρ (Real.rpow_nonneg hL.le _) hd ctr hctr
  unfold coneX
  exact mul_le_mul_of_nonneg_right hcard hB0

/-- **The single-vine label count with the creation cone** (from L6-STEP1's `vine_count_main`). -/
theorem vine_count_cone {g : ℝ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut g M),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) → Step1.Charted M K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (Step1.VCLadderScale K L w P) → ∀ η ρ : ℝ, 1 ≤ ρ * L →
        1 ≤ L ^ (-6 * η) * (ρ * L) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ ρ) → JointCone K L γ δ η w Adm →
        Step1.VineCountInput' K L γ δ ρ (Cf * coneX d L η) C₂ w Adm P 4 := by
  obtain ⟨Cf, C₂, hCf, hC₂, h⟩ := Step1.vine_count_main (g := g) hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hL⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hLL V D _ _ _ M K hMol hM hvine w Adm P hP0 hscale η ρ hρL hθρ hgap hcone => ?_⟩
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hLL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hLi : L⁻¹ ≤ 2 := (inv_le_one_of_one_le₀ hL1').trans (by norm_num)
  intro c β k0 hP
  have hΛ := K.ladderProdVC_ge_one L γ δ P hL1 hδ.1.le hP0
  refine labelSet_cone_le K L γ δ η ρ hL0 (by omega) hρL hθρ w Adm hgap hcone c β k0 hP
    (VineCount.vineF' d L γ δ L⁻¹ Cf C₂ (K.ladderProdVC L γ δ P) K.C.atoms.card 4) ?_ (fun r => ?_) _ ?_
  · have hΛ0 : 0 < K.ladderProdVC L γ δ P := by linarith
    have hC₂0 : 0 ≤ C₂ := by linarith
    have hlog := Real.log_nonneg hL1'
    have hδ0 := hδ.1
    unfold VineCount.vineF'
    positivity
  · exact hL L hLL M K hMol hM hvine w (AdmFix K Adm r) P hP0 (decScale_fix K L w Adm _ hscale r) L⁻¹
      (inv_nonneg.2 hL0.le) hLi (by rw [inv_mul_cancel₀ hL0.ne']) (fun c' β' k0' _ =>
        ball_of_fix K L w Adm r L⁻¹ (inv_nonneg.2 hL0.le) γ δ c' β' k0') c β k0 hP
  · exact vineF'_split _ _ hL1' hδ.1 hCf (by linarith) (by linarith) le_rfl

/-- **The hyper-object label count with the creation cone** (from L6-STEP1's `hyper_count_main`). -/
theorem hyper_count_cone {g : ℝ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut g M)
        (R : Src.HyperLikeRealization g M K.C.atoms K.C.upper K.C.lower) (_h : K.C.shape = .hyper R),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) →
        Step1.Charted (Molecule.eraseBond M R.added) K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (Step1.VCLadderScale K L w P) → ∀ η ρ : ℝ, 1 ≤ ρ * L →
        1 ≤ L ^ (-6 * η) * (ρ * L) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ ρ) → JointCone K L γ δ η w Adm →
        Step1.VineCountInput' K L γ δ ρ (Cf * coneX d L η) C₂ w Adm P 4 := by
  obtain ⟨Cf, C₂, hCf, hC₂, h⟩ := Step1.hyper_count_main (g := g) hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hL⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hLL V D _ _ _ M K R hR hMol hM hvine w Adm P hP0 hscale η ρ hρL hθρ hgap hcone => ?_⟩
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hLL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hLi : L⁻¹ ≤ 2 := (inv_le_one_of_one_le₀ hL1').trans (by norm_num)
  intro c β k0 hP
  have hΛ := K.ladderProdVC_ge_one L γ δ P hL1 hδ.1.le hP0
  refine labelSet_cone_le K L γ δ η ρ hL0 (by omega) hρL hθρ w Adm hgap hcone c β k0 hP
    (VineCount.vineF' d L γ δ L⁻¹ Cf C₂ (K.ladderProdVC L γ δ P) K.C.atoms.card 4) ?_ (fun r => ?_) _ ?_
  · have hΛ0 : 0 < K.ladderProdVC L γ δ P := by linarith
    have hC₂0 : 0 ≤ C₂ := by linarith
    have hlog := Real.log_nonneg hL1'
    have hδ0 := hδ.1
    unfold VineCount.vineF'
    positivity
  · exact hL L hLL M K R hR hMol hM hvine w (AdmFix K Adm r) P hP0 (decScale_fix K L w Adm _ hscale r) L⁻¹
      (inv_nonneg.2 hL0.le) hLi (by rw [inv_mul_cancel₀ hL0.ne']) (fun c' β' k0' _ =>
        ball_of_fix K L w Adm r L⁻¹ (inv_nonneg.2 hL0.le) γ δ c' β' k0') c β k0 hP
  · exact vineF'_split _ _ hL1' hδ.1 hCf (by linarith) (by linarith) le_rfl

/-- **The label count of two double bonds with the creation cone** (from L6-STEP1's `labelSet_le_vineG`). -/
theorem double_count_cone {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {K : Step1.VineCut g M} (S : Step1.DoubleShape K) {L γ δ η : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop}
    (hd : 1 ≤ d) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R ρ : ℝ) (hR : 0 < R) (hρL : 1 ≤ ρ * L)
    (hθρ : 1 ≤ L ^ (-6 * η) * (ρ * L))
    (hgapLow : ∀ κ', Adm κ' → R / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ ρ) (hcone : JointCone K L γ δ η w Adm) :
    Step1.VineCountInputDouble K L γ δ R ρ ((9 ^ d * 5 ^ d * (2 * d)) * coneX d L η) w Adm 0 := by
  have hL0 : 0 < L := by linarith
  intro c β k0 hP
  refine labelSet_cone_le K L γ δ η ρ hL0 hd hρL hθρ w Adm hgap hcone c β k0 hP
    (vineG d L γ δ R L⁻¹ (9 ^ d * 5 ^ d * (2 * d)) 0) ?_ (fun r => ?_) _ ?_
  · have hmin : 0 ≤ min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) := by
      have h1 : 0 ≤ R⁻¹ * L ^ ((d : ℝ) - 2 * γ) := by positivity
      have h2 : (0 : ℝ) ≤ L ^ d := by positivity
      exact le_min h1 h2
    unfold vineG
    positivity
  · exact Step1.DoubleShape.labelSet_le_vineG S (Adm := AdmFix K Adm r) hd hL hδ hδ1 R L⁻¹ hR
      (inv_nonneg.2 hL0.le) (by rw [inv_mul_cancel₀ hL0.ne']) (fun κ' hκ' => hgapLow κ' hκ'.1)
      (fun c' β' k0' _ => ball_of_fix K L w Adm r L⁻¹ (inv_nonneg.2 hL0.le) γ δ c' β' k0') c β k0 hP
  · exact vineG_split _ hL hδ hR (by positivity) le_rfl

end WaveTurbulence.GammaLow.FinalCount.Ghost
