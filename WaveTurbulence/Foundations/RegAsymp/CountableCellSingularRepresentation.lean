/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountableDeltaCellMixture
public import WaveTurbulence.Foundations.ApproxNT.AppRep

/-! # Iterated singular integrals of actual countable Fourier-cell mixtures -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset Function Filter

variable {d n : ℕ}

/-- The actual cell factor after the last k pair integrations. -/
def mixtureAppFactor (J : Finset (Fin n)) (k : ℕ) (p q ξ η x y : Fin n → Mom d) (j : Fin n) : ℂ :=
  if n ≤ j.val+k then cellOp J j (p j) (q j) (ξ j) (η j)
  else cellFn (p j) (q j) (ξ j) (η j) (x j) (y j)

theorem stronglyMeasurable_mixtureAppFactor {U : Type*} [MeasurableSpace U]
    (hd : 3 ≤ d) (J : Finset (Fin n)) (k : ℕ) (p q : Fin n → Mom d)
    (ξ η : U → Fin n → Mom d) (hξ : Measurable ξ) (hη : Measurable η)
    (x y : Fin n → Mom d) (j : Fin n) :
    StronglyMeasurable (fun u => mixtureAppFactor J k p q (ξ u) (η u) x y j) := by
  have hp : Measurable (fun u => (ξ u j,η u j)) :=
    ((measurable_pi_apply j).comp hξ).prodMk ((measurable_pi_apply j).comp hη)
  unfold mixtureAppFactor
  by_cases hj : n ≤ j.val+k
  · simp only [hj,ite_true]
    have hbase : StronglyMeasurable (fun z : Mom d × Mom d => cellOp J j (p j) (q j) z.1 z.2) :=
      stronglyMeasurable_cellOp hd J j (p j) (q j)
    exact hbase.comp_measurable (g := fun u : U => (ξ u j,η u j)) hp
  · simp only [hj,ite_false]
    have hm : Measurable (fun u => ((ξ u j,η u j),(x j,y j))) := hp.prodMk measurable_const
    have hbase : StronglyMeasurable (fun z : (Mom d × Mom d) × (Mom d × Mom d) =>
        cellFn (p j) (q j) z.1.1 z.1.2 z.2.1 z.2.2) :=
      (continuous_cellFn_all (p j) (q j)).stronglyMeasurable
    exact hbase.comp_measurable (g := fun u : U => ((ξ u j,η u j),(x j,y j))) hm

theorem norm_mixtureAppFactor_le {M : ℝ} (hM : 1 ≤ M)
    (hb : ∀ (J : Finset (Fin n)) (j : Fin n) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ M)
    (J : Finset (Fin n)) (k : ℕ) (p q ξ η x y : Fin n → Mom d) (j : Fin n) :
    ‖mixtureAppFactor J k p q ξ η x y j‖ ≤ M := by
  unfold mixtureAppFactor
  split_ifs
  · exact hb _ _ _ _ _ _
  · exact (norm_cellFn_le _ _ _ _ _ _).trans hM

variable {I U : Type*} [Countable I] [MeasurableSpace U] (ν : Measure U) [SFinite ν]

/-- Every intermediate pair integral has the exact countable cell
representation. The coefficient mass is the literal absolute Fourier-cell
mass; no smoothness or compact support of the full mixture is assumed. -/
theorem appIter_countableCellMixture (hd : 3 ≤ d) (J : Finset (Fin n))
    (p q : I → Fin n → Mom d) (ξ η : I → U → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) :
    ∀ k, k ≤ n → ∀ x y,
      appIter J (fun x y => ∑' i, ∫ u, h i u*
        ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) k x y =
      ∑' i, ∫ u, h i u*∏ j, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j ∂ν := by
  obtain ⟨M,hM,hcell⟩ := exists_cellOp_bound hd
  intro k
  induction k with
  | zero =>
    intro _ x y
    change (∑' i, ∫ u, h i u*∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) = _
    apply tsum_congr
    intro i
    apply integral_congr_ae
    apply ae_of_all
    intro u
    dsimp only
    congr 1
    apply prod_congr rfl
    intro j _
    simp only [mixtureAppFactor,Nat.add_zero,not_le.mpr j.isLt,ite_false]
  | succ k ih =>
    intro hk x y
    have hkn : k < n := by omega
    let jk : Fin n := ⟨n-1-k,by omega⟩
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
      rw [ih hkn.le]
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
        have hc : ¬n ≤ jk.val+k := by dsimp only [jk]; omega
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
    have hfin (i : I) (u : U) : hw i u*cellOp J jk (p i jk) (q i jk) (ξ i u jk) (η i u jk) =
        h i u*∏ j, mixtureAppFactor J (k+1) (p i) (q i) (ξ i u) (η i u) x y j := by
      dsimp only [hw]
      rw [← mul_prod_erase univ (fun j => mixtureAppFactor J (k+1) (p i) (q i) (ξ i u) (η i u) x y j) (mem_univ jk)]
      have hjk : mixtureAppFactor J (k+1) (p i) (q i) (ξ i u) (η i u) x y jk =
          cellOp J jk (p i jk) (q i jk) (ξ i u jk) (η i u jk) := by
        have hc : n ≤ jk.val+(k+1) := by dsimp only [jk]; omega
        simp only [mixtureAppFactor,hc,ite_true]
      have hrest : (∏ j ∈ univ.erase jk, mixtureAppFactor J (k+1) (p i) (q i) (ξ i u) (η i u) x y j) =
          ∏ j ∈ univ.erase jk, mixtureAppFactor J k (p i) (q i) (ξ i u) (η i u) x y j := by
        apply prod_congr rfl
        intro j hj
        have hne : j.val ≠ n-1-k := fun he => ne_of_mem_erase hj (Fin.ext he)
        have hc : n ≤ j.val+(k+1) ↔ n ≤ j.val+k := by omega
        simp only [mixtureAppFactor,hc]
      rw [hjk,hrest]
      ring
    have hstep : appIter J (fun x y => ∑' i, ∫ u, h i u*
        ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) (k+1) x y =
        appStep J jk (appIter J (fun x y => ∑' i, ∫ u, h i u*
          ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) k) x y := by
      simp only [appIter,hkn,dite_true,jk]
    rw [hstep,appStep]
    simp_rw [hupd]
    split_ifs with hJ
    · rw [pvOp_tsum_integral_cells ν hd (fun i => p i jk) (fun i => q i jk)
        (fun i u => ξ i u jk) (fun i u => η i u jk) hmeas1 hmeas2 hw hwm hwi hws]
      apply tsum_congr
      intro i
      apply integral_congr_ae
      apply ae_of_all
      intro u
      dsimp only
      rw [← hfin i u]
      simp only [cellOp,hJ,ite_true]
    · rw [deltaInner_tsum_integral_cells ν hd (fun i => p i jk) (fun i => q i jk)
        (fun i u => ξ i u jk) (fun i u => η i u jk) hmeas1 hmeas2 hw hwi hws]
      apply tsum_congr
      intro i
      apply integral_congr_ae
      apply ae_of_all
      intro u
      dsimp only
      rw [← hfin i u]
      simp only [cellOp,hJ,ite_false]

/-- Generic singular-integral/Fubini identity for the actual countable
cell mixture. This applies equally to couple and tree momentum factors. -/
theorem singInt_countableCellMixture (hd : 3 ≤ d) (J : Finset (Fin n))
    (p q : I → Fin n → Mom d) (ξ η : I → U → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) :
    singInt J (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) =
      ∑' i, ∫ u, h i u*∏ j, cellOp J j (p i j) (q i j) (ξ i u j) (η i u j) ∂ν := by
  rw [singInt,appIter_countableCellMixture ν hd J p q ξ η hξ hη h hsm hi hsum n le_rfl]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  apply ae_of_all
  intro u
  simp only [mixtureAppFactor,Nat.le_add_left,ite_true]

end WaveTurbulence.RegAsymp
