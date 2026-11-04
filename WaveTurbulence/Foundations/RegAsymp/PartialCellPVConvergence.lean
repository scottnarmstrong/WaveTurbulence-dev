/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountablePVConvergence
public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation

/-! # Cutoff convergence at every partial singular integration stage -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset Function Filter Topology

/-- Every unintegrated pair of the actual partially integrated cell
mixture has a convergent cutoff principal value. The original coefficient
mass supplies the local bound after all previous singular integrations. -/
theorem tendsto_pvTrunc_appIter_countableCellMixture
    {U I : Type*} [MeasurableSpace U] [Countable I]
    (ν : Measure U) [SFinite ν] {d n : ℕ} (hd : 3 ≤ d) (J : Finset (Fin n))
    (p q : I → Fin n → Mom d) (ξ η : I → U → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν))
    (k : ℕ) (hk : k ≤ n) (jk : Fin n) (hjk : jk.val+k < n) (x y : Fin n → Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun a b =>
      appIter J (fun x y => ∑' i, ∫ u, h i u*
        ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
        k (update x jk a) (update y jk b))) atTop
      (𝓝 (pvOp (fun a b =>
        appIter J (fun x y => ∑' i, ∫ u, h i u*
          ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
          k (update x jk a) (update y jk b)))) := by
  obtain ⟨M,hM,hcell⟩ := exists_cellOp_bound hd
  let hw := fun (i : I) (u : U) => h i u*
    ∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j
  have hprod (i : I) (u : U) :
      ‖∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j‖ ≤ M^(univ.erase jk).card := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _j ∈ univ.erase jk, M := prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => norm_mixtureAppFactor_le hM hcell J k (p i) (q i) (ξ i u) (η i u) x y j)
      _ = _ := prod_const _
  have hwp (i : I) : StronglyMeasurable (fun u =>
      ∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j) :=
    Finset.stronglyMeasurable_fun_prod _ (fun j _ =>
      stronglyMeasurable_mixtureAppFactor hd J k (p i) (q i) (ξ i) (η i) (hξ i) (hη i) x y j)
  have hwm (i : I) : StronglyMeasurable (hw i) := (hsm i).mul (hwp i)
  have hwi (i : I) : Integrable (hw i) ν :=
    (hi i).mul_bdd (c := M^(univ.erase jk).card) (hwp i).aestronglyMeasurable (ae_of_all _ (hprod i))
  have hwL1 (i : I) : (∫ u, ‖hw i u‖ ∂ν) ≤ M^(univ.erase jk).card*(∫ u, ‖h i u‖ ∂ν) := by
    calc
      _ ≤ ∫ u, M^(univ.erase jk).card*‖h i u‖ ∂ν := by
        apply integral_mono (hwi i).norm ((hi i).norm.const_mul _)
        intro u
        change ‖h i u*(∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j)‖ ≤ M^(univ.erase jk).card*‖h i u‖
        rw [norm_mul,mul_comm (M^(univ.erase jk).card)]
        exact mul_le_mul_of_nonneg_left (hprod i u) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have hws : Summable (fun i => ∫ u, ‖hw i u‖ ∂ν) := by
    apply (hsum.mul_left (M^(univ.erase jk).card)).of_norm_bounded
    intro i
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hwL1 i
  have hupd (x' y' : Mom d) :
      appIter J (fun x y => ∑' i, ∫ u, h i u*
        ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
        k (update x jk x') (update y jk y') =
      ∑' i, cellMixture ν (p i jk) (q i jk) (fun u => ξ i u jk) (fun u => η i u jk) (hw i) x' y' := by
    rw [appIter_countableCellMixture ν hd J p q ξ η hξ hη h hsm hi hsum k hk]
    apply tsum_congr
    intro i
    unfold cellMixture
    apply integral_congr_ae
    apply ae_of_all
    intro u
    dsimp only [hw]
    rw [← mul_prod_erase univ _ (mem_univ jk)]
    have hjk : mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) (update x jk x') (update y jk y') jk =
        cellFn (p i jk) (q i jk) (ξ i u jk) (η i u jk) x' y' := by
      have hc : ¬n ≤ jk.val+k := not_le.mpr hjk
      simp only [mixtureAppFactor,hc,ite_false,update_self]
    have hrest : (∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u)
        (update x jk x') (update y jk y') j) =
        ∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j := by
      apply prod_congr rfl
      intro j hj
      simp only [mixtureAppFactor,update_of_ne (ne_of_mem_erase hj)]
    rw [hjk,hrest]
    ring
  have hmeas1 (i : I) : Measurable (fun u => ξ i u jk) := (measurable_pi_apply jk).comp (hξ i)
  have hmeas2 (i : I) : Measurable (fun u => η i u jk) := (measurable_pi_apply jk).comp (hη i)
  have he : (fun a b => appIter J (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
      k (update x jk a) (update y jk b)) =
      (fun a b => ∑' i, cellMixture ν (p i jk) (q i jk)
        (fun u => ξ i u jk) (fun u => η i u jk) (hw i) a b) := by
    funext a b
    exact hupd a b
  rw [he,pvOp_tsum_integral_cells ν hd (fun i => p i jk) (fun i => q i jk)
    (fun i u => ξ i u jk) (fun i u => η i u jk) hmeas1 hmeas2 hw hwm hwi hws]
  exact tendsto_pvTrunc_countableCellMixture ν hd (fun i => p i jk) (fun i => q i jk)
    (fun i u => ξ i u jk) (fun i u => η i u jk) hmeas1 hmeas2 hw hwm hwi hws

end WaveTurbulence.RegAsymp
