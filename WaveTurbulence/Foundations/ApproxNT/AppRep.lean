/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.AppExchange
public import WaveTurbulence.Foundations.ApproxNT.CellSplit

/-!
# The approximation `I_app` of DH23 Prop 6.4 and its cell representation (packet NT6)

DH23 (intappr): `I_app = (L^{2d-2γ}δ⁻¹)^n ∫Ψ₁ · ∫ W ∏_{j∈J} p.v. 1/⟨x_j,y_j⟩ ∏_{j∉J} δ(⟨x_j,y_j⟩)`.
The singular integral is read as iterated integration in the pairs `(x_j, y_j)` (`singInt`, built
from `appStep`, innermost `j = n-1`, as in DH21 L1636 "backwards in `n` starting with the
`dx_n dy_n` integral"): the principal value is `pvOp`, the limit of the
`χ_∞(ν⟨x,y⟩)/⟨x,y⟩` truncations (DH21 Lemma 6.3's `μ`-regularization), and `δ(⟨x,y⟩)` is the
hyperplane reading `NTSP.deltaInner` of ruling D6.

Representation (`appIter_eq`): with the cell partition and Fourier inversion of `W`, after the
pairs `j ≥ n - k` have been integrated,
`appIter k W (x,y) = ∑_{cells} ∫ Ŵ(τ) ∏_{j≥n-k} cellOp_j(τ) ∏_{j<n-k} P_j(τ; x_j, y_j) dτ`,
by the exchange lemmas of `AppExchange`. In particular `singInt J W = ∑ ∫ Ŵ ∏_j cellOp_j`.
-/

public section

noncomputable section

open MeasureTheory Finset Filter Topology Function
open scoped ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-! ### Measurability and boundedness of the cell factors -/

theorem stronglyMeasurable_deltaInner_cellFn (hd : 3 ≤ d) (p q : Mom d) :
    StronglyMeasurable (fun v : Mom d × Mom d => NTSP.deltaInner (cellFn p q v.1 v.2)) := by
  set F : (((Mom d × Mom d) × ℝ) × Mom d) × Mom d → ℂ := fun w =>
    Real.fourierChar (inner ℝ w.2 w.1.1.1.1 + inner ℝ w.1.2 w.1.1.1.2 + w.1.1.2 * inner ℝ w.2 w.1.2) •
      cellAmp p q w.2 w.1.2
  have hF : StronglyMeasurable F := by
    refine Continuous.stronglyMeasurable ?_
    simp only [F, cellAmp, Circle.smul_def, smul_eq_mul]
    have h1 : Continuous fun w : (((Mom d × Mom d) × ℝ) × Mom d) × Mom d =>
        inner ℝ w.2 w.1.1.1.1 + inner ℝ w.1.2 w.1.1.1.2 + w.1.1.2 * inner ℝ w.2 w.1.2 := by
      fun_prop
    refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp h1)).mul ?_
    exact (continuous_thetaC.comp (continuous_snd.sub continuous_const)).mul
      (continuous_thetaC.comp ((continuous_snd.comp continuous_fst).sub continuous_const))
  have h3 := (hF.integral_prod_right' (ν := volume)).integral_prod_right' (ν := volume)
    |>.integral_prod_right' (ν := volume)
  have heq : (fun v : Mom d × Mom d => NTSP.deltaInner (cellFn p q v.1 v.2)) =
      fun v => ∫ s : ℝ, ∫ y : Mom d, ∫ x : Mom d, F (((v, s), y), x) := by
    funext v
    rw [deltaInner_cellFn hd]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [F]
    rw [cellInt_eq]
  rw [heq]
  exact h3

theorem stronglyMeasurable_pvOp_cellFn (hd : 3 ≤ d) (p q : Mom d) :
    StronglyMeasurable (fun v : Mom d × Mom d => pvOp (cellFn p q v.1 v.2)) := by
  obtain ⟨M, -, hM⟩ := exists_pvCell hd
  have hm : ∀ m : ℕ, StronglyMeasurable (fun v : Mom d × Mom d =>
      pvTrunc ((m : ℝ) + 1) (cellFn p q v.1 v.2)) := fun m => by
    set G : ((Mom d × Mom d) × Mom d) × Mom d → ℂ := fun w =>
      pvKer ((m : ℝ) + 1) w.1.2 w.2 * cellFn p q w.1.1.1 w.1.1.2 w.1.2 w.2
    have hG : StronglyMeasurable G := by
      refine Measurable.stronglyMeasurable ?_
      have h1 : Measurable (fun w : ((Mom d × Mom d) × Mom d) × Mom d => (w.1.2, w.2)) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have h2 := (measurable_pvKer (d := d) ((m : ℝ) + 1)).comp h1
      have h3 : Measurable (fun w : ((Mom d × Mom d) × Mom d) × Mom d =>
          ((w.1.1.1, w.1.1.2), (w.1.2, w.2))) :=
        (((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).comp measurable_fst)).prodMk h1
      have h4 := (continuous_cellFn_all p q).measurable.comp h3
      have h5 := h2.mul h4
      exact h5
    have h6 := (hG.integral_prod_right' (ν := volume)).integral_prod_right' (ν := volume)
    have heq : (fun v : Mom d × Mom d => pvTrunc ((m : ℝ) + 1) (cellFn p q v.1 v.2)) =
        fun v => ∫ x : Mom d, ∫ y : Mom d, G ((v, x), y) := by
      funext v
      rw [pvTrunc_eq_integral]
      rfl
    rw [heq]
    exact h6
  refine stronglyMeasurable_of_tendsto atTop hm (tendsto_pi_nhds.2 fun v => ?_)
  have ht : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact ((hM p q v.1 v.2).2.1).comp ht

theorem stronglyMeasurable_cellOp (hd : 3 ≤ d) {ι : Type*} [DecidableEq ι] (J : Finset ι) (j : ι)
    (p q : Mom d) : StronglyMeasurable (fun v : Mom d × Mom d => cellOp J j p q v.1 v.2) := by
  unfold cellOp
  split_ifs
  · exact stronglyMeasurable_pvOp_cellFn hd p q
  · exact stronglyMeasurable_deltaInner_cellFn hd p q

theorem exists_cellOp_bound (hd : 3 ≤ d) : ∃ Mo : ℝ, 1 ≤ Mo ∧
    ∀ {ι : Type*} [DecidableEq ι] (J : Finset ι) (j : ι) (p q ξ η : Mom d),
      ‖cellOp J j p q ξ η‖ ≤ Mo := by
  obtain ⟨M, -, hM⟩ := exists_pvCell hd
  refine ⟨max M (cellCa d), le_max_of_le_right (one_le_cellCa d), fun J j p q ξ η => ?_⟩
  unfold cellOp
  split_ifs
  · exact ((hM p q ξ η).2.2.1).trans (le_max_left _ _)
  · exact (norm_deltaInner_cellFn_le hd p q ξ η).trans (le_max_right _ _)

theorem norm_cellFn_le (p q ξ η x y : Mom d) : ‖cellFn p q ξ η x y‖ ≤ 1 := by
  rw [norm_cellFn]; exact norm_cellAmp_le_one _ _ _ _

/-! ### `I_app` -/

variable {n : ℕ}

/-- The `j`-th factor of `I_app` applied to `G` in the pair `(x_j, y_j)`:
`p.v. ∫∫ G(…x_j…; …y_j…) / ⟨x_j, y_j⟩ dx_j dy_j` for `j ∈ J`,
`∫∫ δ(⟨x_j, y_j⟩) G(…x_j…; …y_j…) dx_j dy_j` (hyperplane reading, D6) otherwise. -/
@[expose] def appStep (J : Finset (Fin n)) (j : Fin n)
    (G : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (x y : Fin n → Mom d) : ℂ :=
  if j ∈ J then pvOp (fun x' y' => G (update x j x') (update y j y'))
  else NTSP.deltaInner (fun x' y' => G (update x j x') (update y j y'))

/-- The factors `j ≥ n - k` applied to `G`, backwards from `j = n - 1` (the innermost). -/
@[expose] def appIter (J : Finset (Fin n)) (G : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) :
    ℕ → (Fin n → Mom d) → (Fin n → Mom d) → ℂ
  | 0 => G
  | k + 1 => if hk : k < n then appStep J ⟨n - 1 - k, by omega⟩ (appIter J G k) else appIter J G k

/-- `∫_{(ℝ^d)^{2n}} W ∏_{j∈J} p.v. 1/⟨x_j,y_j⟩ ∏_{j∉J} δ(⟨x_j,y_j⟩)`, integrating one pair
`(x_j, y_j)` at a time, `j = n-1` first. -/
@[expose] def singInt (J : Finset (Fin n)) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) : ℂ :=
  appIter J W n 0 0

/-- **DH23 (intappr)**:
`I_app = (L^{2d-2γ} δ⁻¹)^n ∫ Ψ₁ dΩ[J^c] · ∫ W ∏_{j∈J} p.v. 1/⟨x_j,y_j⟩ ∏_{j∉J} δ(⟨x_j,y_j⟩)`. -/
@[expose] def approxApp (L δ γ : ℝ) (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) : ℂ :=
  ((L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹ : ℝ) : ℂ) ^ n * (∫ Ω, Ψ₁ Ω) * singInt J W

/-! ### The cell representation -/

/-- The factors of one product of cells after the pairs `j ≥ n - k` have been integrated. -/
@[expose] def appFac (J : Finset (Fin n)) (k : ℕ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) (x y : Fin n → Mom d) (j : Fin n) : ℂ :=
  if n ≤ (j : ℕ) + k then cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)
  else cellFn (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j) (x j) (y j)

theorem aestronglyMeasurable_appFac (hd : 3 ≤ d) (J : Finset (Fin n)) (k : ℕ)
    (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (x y : Fin n → Mom d) (j : Fin n) :
    StronglyMeasurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => appFac J k pq τ x y j) := by
  have hτ : Measurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => (τ.1 j, τ.2 j)) :=
    ((measurable_pi_apply j).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
  unfold appFac
  split_ifs
  · have h := (stronglyMeasurable_cellOp hd J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)).comp_measurable hτ
    exact h
  · have h1 : Continuous (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
        ((τ.1 j, τ.2 j), (x j, y j))) := by fun_prop
    have h2 := (continuous_cellFn_all (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)).comp h1
    exact h2.stronglyMeasurable

theorem norm_appFac_le {Mo : ℝ} (hMo : 1 ≤ Mo)
    (hb : ∀ (J : Finset (Fin n)) (j : Fin n) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ Mo)
    (J : Finset (Fin n)) (k : ℕ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) (x y : Fin n → Mom d) (j : Fin n) :
    ‖appFac J k pq τ x y j‖ ≤ Mo := by
  unfold appFac
  split_ifs
  · exact hb _ _ _ _ _ _
  · exact (norm_cellFn_le _ _ _ _ _ _).trans hMo

/-- **The cell representation of the iterated singular integral.** -/
theorem appIter_eq (hd : 3 ≤ d) (J : Finset (Fin n)) {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (Q : Finset (Fin n → (Fin d → ℤ) × (Fin d → ℤ)))
    (hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2))
    (h0 : ∀ x y, W x y = ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      fourierW W τ.1 τ.2 * ∏ j, appFac J 0 pq τ x y j) :
    ∀ k, k ≤ n → ∀ x y, appIter J W k x y = ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      fourierW W τ.1 τ.2 * ∏ j, appFac J k pq τ x y j := by
  obtain ⟨Mo, hMo, hb⟩ := exists_cellOp_bound hd
  have : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
  intro k
  induction k with
  | zero => intro _ x y; exact h0 x y
  | succ k ih =>
    intro hk x y
    have hkn : k < n := by omega
    set jk : Fin n := ⟨n - 1 - k, by omega⟩
    have hIH := ih hkn.le
    -- the weights
    set hw : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → (Fin n → Mom d) × (Fin n → Mom d) → ℂ :=
      fun pq τ => fourierW W τ.1 τ.2 * ∏ j ∈ univ.erase jk, appFac J k pq τ x y j with hw_def
    have hwi : ∀ pq, Integrable (hw pq) := fun pq => by
      refine hF.mul_bdd (c := Mo ^ (univ.erase jk).card) ?_ (Eventually.of_forall fun τ => ?_)
      · exact (Finset.stronglyMeasurable_fun_prod _ fun j _ =>
          aestronglyMeasurable_appFac hd J k pq x y j).aestronglyMeasurable
      · rw [norm_prod]
        calc ∏ j ∈ univ.erase jk, ‖appFac J k pq τ x y j‖ ≤ ∏ _j ∈ univ.erase jk, Mo :=
              prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => norm_appFac_le hMo
                (fun J j p q ξ η => hb J j p q ξ η) J k pq τ x y j
          _ = _ := prod_const _
    -- the updated function
    have hupd : ∀ x' y', appIter J W k (update x jk x') (update y jk y') =
        ∑ pq ∈ Q, ∫ τ, hw pq τ * cellFn (NTSP.intVec (pq jk).1) (NTSP.intVec (pq jk).2)
          (τ.1 jk) (τ.2 jk) x' y' := fun x' y' => by
      rw [hIH]
      refine sum_congr rfl fun pq _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [hw_def]
      rw [← mul_prod_erase univ _ (mem_univ jk)]
      have hjk : appFac J k pq τ (update x jk x') (update y jk y') jk =
          cellFn (NTSP.intVec (pq jk).1) (NTSP.intVec (pq jk).2) (τ.1 jk) (τ.2 jk) x' y' := by
        have hc : ¬ (n ≤ (jk : ℕ) + k) := by simp only [jk]; omega
        simp only [appFac, hc, ↓reduceIte, update_self]
      have hrest : ∏ j ∈ univ.erase jk, appFac J k pq τ (update x jk x') (update y jk y') j =
          ∏ j ∈ univ.erase jk, appFac J k pq τ x y j :=
        prod_congr rfl fun j hj => by
          have hne := ne_of_mem_erase hj
          simp only [appFac, update_of_ne hne]
      rw [hjk, hrest]
      ring
    have hmeas1 : ∀ pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
        Measurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => τ.1 jk) :=
      fun _ => (measurable_pi_apply jk).comp measurable_fst
    have hmeas2 : ∀ pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
        Measurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => τ.2 jk) :=
      fun _ => (measurable_pi_apply jk).comp measurable_snd
    have hstep : appIter J W (k + 1) x y = appStep J jk (appIter J W k) x y := by
      simp only [appIter, hkn, ↓reduceDIte, jk]
    rw [hstep, appStep]
    simp_rw [hupd]
    have hfin : ∀ pq (τ : (Fin n → Mom d) × (Fin n → Mom d)),
        hw pq τ * cellOp J jk (NTSP.intVec (pq jk).1) (NTSP.intVec (pq jk).2) (τ.1 jk) (τ.2 jk) =
          fourierW W τ.1 τ.2 * ∏ j, appFac J (k + 1) pq τ x y j := fun pq τ => by
      simp only [hw_def]
      rw [← mul_prod_erase univ (fun j => appFac J (k + 1) pq τ x y j) (mem_univ jk)]
      have hjk : appFac J (k + 1) pq τ x y jk =
          cellOp J jk (NTSP.intVec (pq jk).1) (NTSP.intVec (pq jk).2) (τ.1 jk) (τ.2 jk) := by
        have hc : n ≤ (jk : ℕ) + (k + 1) := by simp only [jk]; omega
        simp only [appFac, hc, ↓reduceIte]
      have hrest : ∏ j ∈ univ.erase jk, appFac J (k + 1) pq τ x y j =
          ∏ j ∈ univ.erase jk, appFac J k pq τ x y j :=
        prod_congr rfl fun j hj => by
          have hne : (j : ℕ) ≠ n - 1 - k := fun h => ne_of_mem_erase hj (Fin.ext h)
          have hiff : n ≤ (j : ℕ) + (k + 1) ↔ n ≤ (j : ℕ) + k := by omega
          simp only [appFac, hiff]
      rw [hjk, hrest]
      ring
    split_ifs with hJ
    · rw [pvOp_sum_integral hd Q (fun pq => NTSP.intVec (pq jk).1) (fun pq => NTSP.intVec (pq jk).2)
        hmeas1 hmeas2 hwi]
      refine sum_congr rfl fun pq _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only
      rw [← hfin]
      simp only [cellOp, hJ, ↓reduceIte]
    · rw [deltaInner_sum_integral hd Q (fun pq => NTSP.intVec (pq jk).1)
        (fun pq => NTSP.intVec (pq jk).2) hmeas1 hmeas2 hwi]
      refine sum_congr rfl fun pq _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only
      rw [← hfin]
      simp only [cellOp, hJ, ↓reduceIte]

/-- The iterated singular integral of `W` as a superposition of products of cell factors. -/
theorem singInt_eq (hd : 3 ≤ d) (J : Finset (Fin n)) {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (Q : Finset (Fin n → (Fin d → ℤ) × (Fin d → ℤ)))
    (hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2))
    (h0 : ∀ x y, W x y = ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      fourierW W τ.1 τ.2 * ∏ j, appFac J 0 pq τ x y j) :
    singInt J W = ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
      ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j) := by
  rw [singInt, appIter_eq hd J Q hF h0 n le_rfl]
  refine sum_congr rfl fun pq _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [appFac, Nat.le_add_left, ↓reduceIte]

end WaveTurbulence.ApproxNT
