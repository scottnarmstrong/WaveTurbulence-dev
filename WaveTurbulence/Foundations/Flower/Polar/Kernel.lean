/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Pointwise
public import WaveTurbulence.Foundations.XChain.GraftGenDraft.KernelGenGraft
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! # FL-POLAR: the decoration-sum interchange for `kernelKgen` with a weight family, and summability of
the kernel summand for weights dominated by a product of input-leaf decays. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset GraftGen

variable {w d : ℕ}

theorem jbr_pos_p (x : Mom d) : 0 < jbr x := Real.sqrt_pos.2 (by positivity)

theorem kernelGenFactor_eq_mul (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d n nfl) :
    kernelGenFactor L γ δ F LG fix off wt up k₀ κ =
      (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
        kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ := by
  unfold kernelGenFactor; push_cast; ring

/-- The decoration-sum interchange: if `x · wt0 = ∑_m a_m wt_m` on all decorations and every `wt_m`
has a summable kernel summand, then `x · K[wt0] = ∑_m a_m K[wt_m]`. -/
theorem kernelKgen_linear_step {ι : Type*} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (T : Finset ι) (a : ι → ℝ) (x : ℝ)
    (wt0 : (GNode LG.garden.tree → Mom d) → ℝ) (wt : ι → (GNode LG.garden.tree → Mom d) → ℝ)
    (hpt : ∀ κ : GenDecoration LG.garden d n nfl,
      x * wt0 (cosetDecoration LG.garden L k₀ κ.1) =
        ∑ m ∈ T, a m * wt m (cosetDecoration LG.garden L k₀ κ.1))
    (hs : ∀ m ∈ T, Summable (kernelGenFactor L γ δ F LG fix off (wt m) up k₀ (n := n) (nfl := nfl))) :
    (x : ℂ) * kernelKgen L γ δ F LG fix off wt0 up k₀ n nfl =
      ∑ m ∈ T, (a m : ℂ) * kernelKgen L γ δ F LG fix off (wt m) up k₀ n nfl := by
  simp only [kernelKgen_eq_tsum]
  set C : ℂ := (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta with hC
  have hpt' : ∀ κ : GenDecoration LG.garden d n nfl,
      (x : ℂ) * kernelGenFactor L γ δ F LG fix off wt0 up k₀ κ =
        ∑ m ∈ T, (a m : ℂ) * kernelGenFactor L γ δ F LG fix off (wt m) up k₀ κ := by
    intro κ
    rw [kernelGenFactor_eq_mul, Finset.sum_congr rfl fun m _ => by rw [kernelGenFactor_eq_mul]]
    have := congrArg (fun r : ℝ => (r : ℂ)) (hpt κ)
    simp only [Complex.ofReal_mul, Complex.ofReal_sum] at this
    calc (x : ℂ) * ((wt0 (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
          kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ)
        = ((x : ℂ) * (wt0 (cosetDecoration LG.garden L k₀ κ.1) : ℂ)) *
          kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ := by ring
      _ = _ := by rw [this, Finset.sum_mul]; refine sum_congr rfl fun m _ => by ring
  calc (x : ℂ) * (C * ∑' κ, kernelGenFactor L γ δ F LG fix off wt0 up k₀ κ)
      = C * ∑' κ, (x : ℂ) * kernelGenFactor L γ δ F LG fix off wt0 up k₀ κ := by
        rw [tsum_mul_left]; ring
    _ = C * ∑' κ : GenDecoration LG.garden d n nfl,
          ∑ m ∈ T, (a m : ℂ) * kernelGenFactor L γ δ F LG fix off (wt m) up k₀ κ := by
        simp_rw [hpt']
    _ = C * ∑ m ∈ T, ∑' κ : GenDecoration LG.garden d n nfl,
          (a m : ℂ) * kernelGenFactor L γ δ F LG fix off (wt m) up k₀ κ := by
        rw [Summable.tsum_finsetSum fun m hm => (hs m hm).mul_left _]
    _ = _ := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [tsum_mul_left]; ring

theorem sibWeight_abs_le_one (LG : LayeredGarden w) (c : Fin w → Fin 3 → Mom d)
    (k : GNode LG.garden.tree → Mom d) : |LG.sibWeight c k| ≤ 1 := by
  unfold LayeredGarden.sibWeight
  have h0 : 0 ≤ ∏ b : GBranch LG.garden.tree, if LG.garden.IsFlowerParent b then
      ∏ i : Fin 3, (if LG.IsFlowerNode (b.child i) then (1 : ℝ) else
        if k (b.child i) = c b.1.1 i then 1 else 0) else 1 := by
    refine Finset.prod_nonneg fun b _ => ?_
    split_ifs
    · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
    · norm_num
  rw [abs_of_nonneg h0]
  refine Finset.prod_le_one₀ (fun b _ => ?_) fun b _ => ?_
  · split_ifs
    · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
    · norm_num
  · split_ifs
    · exact Finset.prod_le_one₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by split_ifs <;> norm_num
    · norm_num

/-- Summability of the kernel summand (`F ≡ 1`) for weights dominated by a product of input-leaf decays. -/
theorem summable_kernelGenFactor_dom (L γ δ : ℝ) (hL : 1 ≤ L) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower)
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hwt : ∀ k, |wt k| ≤ ∏ ℓ ∈ inputLeaves LG.garden, (C * jbr (k ℓ.toNode) ^ (-((d + 1 : ℕ) : ℝ)))) :
    Summable (kernelGenFactor L γ δ (fun _ _ => 1) LG fix off wt up 0 (n := n) (nfl := nfl)) := by
  set F : ℕ → Mom d → ℝ := fun _ x => C * jbr x ^ (-((d + 1 : ℕ) : ℝ)) with hFdef
  have hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (0 + latticePoint L m)| := by
    intro q
    refine ((LGSpine.summable_jbr_coset_neg hL (0 : Mom d)).mul_left C).congr fun m => ?_
    simp only [hFdef]
    rw [abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (jbr_pos_p _).le _))]
    push_cast; rfl
  have hsum := summable_kernelGenFactor L γ δ F LG fix off (fun _ => 1) (fun _ => by simp) up 0 n nfl hn hF
  have hnorm : Summable fun κ => ‖kernelGenFactor L γ δ F LG fix off (fun _ => 1) up 0
      (n := n) (nfl := nfl) κ‖ := hsum.norm
  refine Summable.of_norm_bounded hnorm fun κ => ?_
  have e1 : ‖kernelGenFactor L γ δ (fun _ _ => 1) LG fix off wt up 0 κ‖ =
      ‖(epsDec LG.garden κ.1 : ℂ)‖ * ‖genIntegral L γ δ LG fix off up (cosetDecoration LG.garden L 0 κ.1)‖ *
        |wt (cosetDecoration LG.garden L 0 κ.1)| := by
    unfold kernelGenFactor
    simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs, norm_one, Finset.prod_const_one,
      mul_one]
    ring
  have e2 : ‖kernelGenFactor L γ δ F LG fix off (fun _ => 1) up 0 κ‖ =
      ‖(epsDec LG.garden κ.1 : ℂ)‖ * ‖genIntegral L γ δ LG fix off up (cosetDecoration LG.garden L 0 κ.1)‖ *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (C * jbr (cosetDecoration LG.garden L 0 κ.1 ℓ.toNode) ^ (-((d + 1 : ℕ) : ℝ))) := by
    unfold kernelGenFactor
    simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_one, one_mul, mul_one]
    congr 1
    refine prod_congr rfl fun ℓ _ => ?_
    simp only [hFdef]
    exact abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (jbr_pos_p _).le _))
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (hwt _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end WaveTurbulence.Flower.Polar
