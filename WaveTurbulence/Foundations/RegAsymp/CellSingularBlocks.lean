/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation
public import WaveTurbulence.Foundations.RegAsymp.CountablePVConvergence

/-! # Actual singular integration along blocks of distinct source pair indices -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset Function Filter Topology

variable {d n : ℕ}

/-- Integrate the original pair operators in the given outer-to-inner list order. -/
def appAlong (J : Finset (Fin n)) : List (Fin n) →
    ((Fin n → Mom d) → (Fin n → Mom d) → ℂ) →
    (Fin n → Mom d) → (Fin n → Mom d) → ℂ
  | [], W => W
  | j::L, W => appStep J j (appAlong J L W)

/-- Each processed cell contributes its actual delta/PV value. -/
def blockCellFactor (J : Finset (Fin n)) (L : List (Fin n))
    (p q ξ η x y : Fin n → Mom d) (j : Fin n) : ℂ :=
  if j ∈ L then cellOp J j (p j) (q j) (ξ j) (η j)
  else cellFn (p j) (q j) (ξ j) (η j) (x j) (y j)

theorem stronglyMeasurable_blockCellFactor {U : Type*} [MeasurableSpace U]
    (hd : 3 ≤ d) (J : Finset (Fin n)) (L : List (Fin n)) (p q : Fin n → Mom d)
    (ξ η : U → Fin n → Mom d) (hξ : Measurable ξ) (hη : Measurable η)
    (x y : Fin n → Mom d) (j : Fin n) :
    StronglyMeasurable (fun u => blockCellFactor J L p q (ξ u) (η u) x y j) := by
  unfold blockCellFactor
  by_cases hj : j ∈ L
  · simp only [hj,ite_true]
    have hm : Measurable (fun u => (ξ u j,η u j)) :=
      ((measurable_pi_apply j).comp hξ).prodMk ((measurable_pi_apply j).comp hη)
    have hbase : StronglyMeasurable (fun z : Mom d × Mom d => cellOp J j (p j) (q j) z.1 z.2) :=
      stronglyMeasurable_cellOp hd J j (p j) (q j)
    exact hbase.comp_measurable (g := fun u : U => (ξ u j,η u j)) hm
  · simp only [hj,ite_false]
    have hm : Measurable (fun u => ((ξ u j,η u j),(x j,y j))) :=
      (((measurable_pi_apply j).comp hξ).prodMk ((measurable_pi_apply j).comp hη)).prodMk measurable_const
    have hbase : StronglyMeasurable (fun z : (Mom d × Mom d) × (Mom d × Mom d) =>
        cellFn (p j) (q j) z.1.1 z.1.2 z.2.1 z.2.2) := (continuous_cellFn_all _ _).stronglyMeasurable
    exact hbase.comp_measurable (g := fun u : U => ((ξ u j,η u j),(x j,y j))) hm

theorem norm_blockCellFactor_le {M : ℝ} (hM : 1 ≤ M)
    (hb : ∀ (J : Finset (Fin n)) (j : Fin n) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ M)
    (J : Finset (Fin n)) (L : List (Fin n)) (p q ξ η x y : Fin n → Mom d) (j : Fin n) :
    ‖blockCellFactor J L p q ξ η x y j‖ ≤ M := by
  unfold blockCellFactor
  split_ifs
  · exact hb J j _ _ _ _
  · exact (norm_cellFn_le _ _ _ _ _ _).trans hM

/-- Blockwise integration is justified on the actual countable-cell
class by original coefficient L1 mass, for every nodup index list. -/
theorem appAlong_countableCellMixture
    {U I : Type*} [MeasurableSpace U] [Countable I]
    (ν : Measure U) [SFinite ν] (hd : 3 ≤ d) (J : Finset (Fin n))
    (p q : I → Fin n → Mom d) (ξ η : I → U → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν))
    (L : List (Fin n)) (hL : L.Nodup) (x y : Fin n → Mom d) :
    appAlong J L (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) x y =
      ∑' i, ∫ u, h i u*∏ j, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j ∂ν := by
  classical
  obtain ⟨M,hM,hcell⟩ := exists_cellOp_bound hd
  induction L generalizing x y with
  | nil => simp only [appAlong,blockCellFactor,List.not_mem_nil,ite_false]
  | cons jk L ih =>
    have hjk : jk ∉ L := (List.nodup_cons.mp hL).1
    have hnd : L.Nodup := (List.nodup_cons.mp hL).2
    let hw := fun (i : I) (u : U) => h i u*
      ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j
    have hprod (i : I) (u : U) :
        ‖∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j‖ ≤ M^(univ.erase jk).card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _j ∈ univ.erase jk, M := prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => norm_blockCellFactor_le hM hcell J L (p i) (q i) (ξ i u) (η i u) x y j)
        _ = _ := prod_const _
    have hwp (i : I) : StronglyMeasurable (fun u =>
        ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j) :=
      Finset.stronglyMeasurable_fun_prod _ (fun j _ =>
        stronglyMeasurable_blockCellFactor hd J L (p i) (q i) (ξ i) (η i) (hξ i) (hη i) x y j)
    have hwm (i : I) : StronglyMeasurable (hw i) := (hsm i).mul (hwp i)
    have hwi (i : I) : Integrable (hw i) ν :=
      (hi i).mul_bdd (c := M^(univ.erase jk).card) (hwp i).aestronglyMeasurable (ae_of_all _ (hprod i))
    have hwL1 (i : I) : (∫ u, ‖hw i u‖ ∂ν) ≤ M^(univ.erase jk).card*(∫ u, ‖h i u‖ ∂ν) := by
      calc
        _ ≤ ∫ u, M^(univ.erase jk).card*‖h i u‖ ∂ν := by
          apply integral_mono (hwi i).norm ((hi i).norm.const_mul _)
          intro u
          change ‖h i u*(∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j)‖ ≤ M^(univ.erase jk).card*‖h i u‖
          rw [norm_mul,mul_comm (M^(univ.erase jk).card)]
          exact mul_le_mul_of_nonneg_left (hprod i u) (norm_nonneg _)
        _ = _ := integral_const_mul _ _
    have hws : Summable (fun i => ∫ u, ‖hw i u‖ ∂ν) := by
      apply (hsum.mul_left (M^(univ.erase jk).card)).of_norm_bounded
      intro i
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hwL1 i
    have hupd (x' y' : Mom d) :
        appAlong J L (fun x y => ∑' i, ∫ u, h i u*
          ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
          (update x jk x') (update y jk y') =
        ∑' i, cellMixture ν (p i jk) (q i jk) (fun u => ξ i u jk) (fun u => η i u jk) (hw i) x' y' := by
      rw [ih hnd]
      apply tsum_congr
      intro i
      unfold cellMixture
      apply integral_congr_ae
      apply ae_of_all
      intro u
      dsimp only [hw]
      rw [← mul_prod_erase univ _ (mem_univ jk)]
      have hjk : blockCellFactor J L (p i) (q i) (ξ i u) (η i u) (update x jk x') (update y jk y') jk =
          cellFn (p i jk) (q i jk) (ξ i u jk) (η i u jk) x' y' := by
        have hc : jk ∉ L := hjk
        simp only [blockCellFactor,hc,ite_false,update_self]
      have hrest : (∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u)
          (update x jk x') (update y jk y') j) =
          ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j := by
        apply prod_congr rfl
        intro j hj
        simp only [blockCellFactor,update_of_ne (ne_of_mem_erase hj)]
      rw [hjk,hrest]
      ring
    have hmeas1 (i : I) : Measurable (fun u => ξ i u jk) := (measurable_pi_apply jk).comp (hξ i)
    have hmeas2 (i : I) : Measurable (fun u => η i u jk) := (measurable_pi_apply jk).comp (hη i)
    have hfin (i : I) (u : U) : hw i u*cellOp J jk (p i jk) (q i jk) (ξ i u jk) (η i u jk) =
        h i u*∏ j, blockCellFactor J (jk::L) (p i) (q i) (ξ i u) (η i u) x y j := by
      dsimp only [hw]
      rw [← mul_prod_erase univ (fun j => blockCellFactor J (jk::L) (p i) (q i) (ξ i u) (η i u) x y j) (mem_univ jk)]
      have hjk : blockCellFactor J (jk::L) (p i) (q i) (ξ i u) (η i u) x y jk =
          cellOp J jk (p i jk) (q i jk) (ξ i u jk) (η i u jk) := by
        simp only [blockCellFactor,List.mem_cons_self,ite_true]
      have hrest : (∏ j ∈ univ.erase jk, blockCellFactor J (jk::L) (p i) (q i) (ξ i u) (η i u) x y j) =
          ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j := by
        apply prod_congr rfl
        intro j hj
        have hne : j ≠ jk := ne_of_mem_erase hj
        simp only [blockCellFactor,List.mem_cons,hne,false_or]
      rw [hjk,hrest]
      ring
    change appStep J jk (appAlong J L (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)) x y = _
    unfold appStep
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

/-- Complete integration blocks equal the original singInt, for any
nodup enumeration. The convergent cell representation justifies the order. -/
theorem appAlong_eq_singInt_countableCellMixture
    {U I : Type*} [MeasurableSpace U] [Countable I]
    (ν : Measure U) [SFinite ν] (hd : 3 ≤ d) (J : Finset (Fin n))
    (p q : I → Fin n → Mom d) (ξ η : I → U → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν))
    (L : List (Fin n)) (hL : L.Nodup) (hcover : ∀ j, j ∈ L) (x y : Fin n → Mom d) :
    appAlong J L (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) x y =
    singInt J (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) := by
  rw [appAlong_countableCellMixture ν hd J p q ξ η hξ hη h hsm hi hsum L hL,
    singInt_countableCellMixture ν hd J p q ξ η hξ hη h hsm hi hsum]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  apply ae_of_all
  intro u
  simp only [blockCellFactor,hcover,ite_true]

/-- Every remaining pair after an actual nodup integration block has a
convergent PV cutoff, with its absolute mass derived from the original
coefficient mass and the already integrated local cell bounds. -/
theorem tendsto_pvTrunc_appAlong_countableCellMixture
    {U I : Type*} [MeasurableSpace U] [Countable I]
    (ν : Measure U) [SFinite ν] {d n : ℕ} (hd : 3 ≤ d) (J : Finset (Fin n))
    (p q : I → Fin n → Mom d) (ξ η : I → U → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν))
    (L : List (Fin n)) (hL : L.Nodup) (jk : Fin n) (hjk : jk ∉ L) (x y : Fin n → Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun a b =>
      appAlong J L (fun x y => ∑' i, ∫ u, h i u*
        ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
        (update x jk a) (update y jk b))) atTop
      (𝓝 (pvOp (fun a b =>
        appAlong J L (fun x y => ∑' i, ∫ u, h i u*
          ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
          (update x jk a) (update y jk b)))) := by
  obtain ⟨M,hM,hcell⟩ := exists_cellOp_bound hd
  let hw := fun (i : I) (u : U) => h i u*
    ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j
  have hprod (i : I) (u : U) :
      ‖∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j‖ ≤ M^(univ.erase jk).card := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _j ∈ univ.erase jk, M := prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => norm_blockCellFactor_le hM hcell J L (p i) (q i) (ξ i u) (η i u) x y j)
      _ = _ := prod_const _
  have hwp (i : I) : StronglyMeasurable (fun u =>
      ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j) :=
    Finset.stronglyMeasurable_fun_prod _ (fun j _ =>
      stronglyMeasurable_blockCellFactor hd J L (p i) (q i) (ξ i) (η i) (hξ i) (hη i) x y j)
  have hwm (i : I) : StronglyMeasurable (hw i) := (hsm i).mul (hwp i)
  have hwi (i : I) : Integrable (hw i) ν :=
    (hi i).mul_bdd (c := M^(univ.erase jk).card) (hwp i).aestronglyMeasurable (ae_of_all _ (hprod i))
  have hwL1 (i : I) : (∫ u, ‖hw i u‖ ∂ν) ≤ M^(univ.erase jk).card*(∫ u, ‖h i u‖ ∂ν) := by
    calc
      _ ≤ ∫ u, M^(univ.erase jk).card*‖h i u‖ ∂ν := by
        apply integral_mono (hwi i).norm ((hi i).norm.const_mul _)
        intro u
        change ‖h i u*(∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j)‖ ≤ M^(univ.erase jk).card*‖h i u‖
        rw [norm_mul,mul_comm (M^(univ.erase jk).card)]
        exact mul_le_mul_of_nonneg_left (hprod i u) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have hws : Summable (fun i => ∫ u, ‖hw i u‖ ∂ν) := by
    apply (hsum.mul_left (M^(univ.erase jk).card)).of_norm_bounded
    intro i
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hwL1 i
  have hupd (x' y' : Mom d) :
      appAlong J L (fun x y => ∑' i, ∫ u, h i u*
        ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
        (update x jk x') (update y jk y') =
      ∑' i, cellMixture ν (p i jk) (q i jk) (fun u => ξ i u jk) (fun u => η i u jk) (hw i) x' y' := by
    rw [appAlong_countableCellMixture ν hd J p q ξ η hξ hη h hsm hi hsum L hL]
    apply tsum_congr
    intro i
    unfold cellMixture
    apply integral_congr_ae
    apply ae_of_all
    intro u
    dsimp only [hw]
    rw [← mul_prod_erase univ _ (mem_univ jk)]
    have hjk : blockCellFactor J L (p i) (q i) (ξ i u) (η i u) (update x jk x') (update y jk y') jk =
        cellFn (p i jk) (q i jk) (ξ i u jk) (η i u jk) x' y' := by
      have hc : jk ∉ L := hjk
      simp only [blockCellFactor,hc,ite_false,update_self]
    have hrest : (∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u)
        (update x jk x') (update y jk y') j) =
        ∏ j ∈ univ.erase jk, blockCellFactor J L (p i) (q i) (ξ i u) (η i u) x y j := by
      apply prod_congr rfl
      intro j hj
      simp only [blockCellFactor,update_of_ne (ne_of_mem_erase hj)]
    rw [hjk,hrest]
    ring
  have hmeas1 (i : I) : Measurable (fun u => ξ i u jk) := (measurable_pi_apply jk).comp (hξ i)
  have hmeas2 (i : I) : Measurable (fun u => η i u jk) := (measurable_pi_apply jk).comp (hη i)
  have he : (fun a b => appAlong J L (fun x y => ∑' i, ∫ u, h i u*
      ∏ j, cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν)
      (update x jk a) (update y jk b)) =
      (fun a b => ∑' i, cellMixture ν (p i jk) (q i jk)
        (fun u => ξ i u jk) (fun u => η i u jk) (hw i) a b) := by
    funext a b
    exact hupd a b
  rw [he,pvOp_tsum_integral_cells ν hd (fun i => p i jk) (fun i => q i jk)
    (fun i u => ξ i u jk) (fun i u => η i u jk) hmeas1 hmeas2 hw hwm hwi hws]
  exact tendsto_pvTrunc_countableCellMixture ν hd (fun i => p i jk) (fun i => q i jk)
    (fun i u => ξ i u jk) (fun i u => η i u jk) hmeas1 hmeas2 hw hwm hwi hws

end WaveTurbulence.RegAsymp
