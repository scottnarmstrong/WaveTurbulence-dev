/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH3
public import WaveTurbulence.Foundations.Stage1.Represents.RepNode2

/-!
# S2 REPRESENTS, VINE-D (4): weights of the hinge modes

`hasSum_prod_real`: the real dependent finite product of summable non-negative families sums to the product of the
sums.  `norm_hingeTerm_le`: the hinge part of an assembled mode is bounded by the product of its weights.
`summable_hingeWeight`: the weights `‖slotTerm ξ‖ · Π_j w_j(ζ_j)` of the assembled modes `⟨ξ, ζ⟩` are summable when the
hinge masses are bounded uniformly in the centres.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

theorem norm_hingeFactor_le {J : Type} (H : HingeFam J d) (j : J) (c : Fin 4 → Fin d → ℤ) (l : H.Λ j c)
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    ‖(H.w j c l : ℂ) * H.a j c l E * fsPhase (H.m j c l) t‖ ≤ H.w j c l := by
  rw [norm_mul, norm_mul, fsPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (H.w_nn j c l)]
  exact mul_le_of_le_one_right (H.w_nn j c l) (H.a_one j c l E)

theorem hasSum_prod_real {ι : Type} [Fintype ι] {M : ι → Type} (u : ∀ i, M i → ℝ) (hu : ∀ i m, 0 ≤ u i m)
    (hs : ∀ i, Summable (u i)) :
    HasSum (fun m : ∀ i, M i => ∏ i, u i (m i)) (∏ i, ∑' m, u i m) := by
  have h := (hasSum_prod_fintype (fun i m => ((u i m : ℝ) : ℂ))
    (fun i => (hs i).congr fun m => by rw [Complex.norm_real, Real.norm_of_nonneg (hu i m)])).2
  rw [← Complex.hasSum_ofReal]
  simp only [Complex.ofReal_prod, Complex.ofReal_tsum]
  exact h

theorem norm_hingeTerm_le (fam : SlotFam S d) (hS : S.IsPlain) {J : Type} [Fintype J] (H : HingeFam J d)
    (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S) (L : ℝ) (base : Mom d) (tt : Fin w → ℝ)
    (ξh : XiH fam hS H hmom) (κ : GNode S.tree → Fin d → ℤ) (τ : GBranch S.tree → ℝ) :
    ‖hingeTerm fam hS H hmom hclk L base tt ξh κ τ‖ ≤ ∏ j, H.w j _ (ξh.2 j) := by
  unfold hingeTerm
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => norm_hingeFactor_le H j _ _ _ _

theorem summable_hingeWeight (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (L : ℝ) (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    {J : Type} [Fintype J] (H : HingeFam J d) (hmom : J → Fin 4 → GNode S.tree) (Mh : J → ℝ)
    (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j) (κ : GNode S.tree → Fin d → ℤ) (τ : GBranch S.tree → ℝ) :
    Summable (fun ξh : XiH fam hS H hmom =>
      ‖slotTerm fam hS Cχ L base roots tt ξh.1 κ τ‖ * ∏ j, H.w j _ (ξh.2 j)) := by
  have hnn : ∀ ξh : XiH fam hS H hmom, 0 ≤ ‖slotTerm fam hS Cχ L base roots tt ξh.1 κ τ‖ * ∏ j, H.w j _ (ξh.2 j) :=
    fun ξh => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ => H.w_nn j _ _)
  have hin : ∀ ξ : XiT fam, HasSum (fun ζ : (∀ j, H.Λ j (hingeCen fam hS hmom ξ j)) =>
      ‖slotTerm fam hS Cχ L base roots tt ξ κ τ‖ * ∏ j, H.w j _ (ζ j))
      (‖slotTerm fam hS Cχ L base roots tt ξ κ τ‖ * ∏ j, ∑' l, H.w j (hingeCen fam hS hmom ξ j) l) := fun ξ =>
    (hasSum_prod_real (fun j l => H.w j (hingeCen fam hS hmom ξ j) l) (fun j l => H.w_nn j _ l)
      (fun j => H.w_sum j _)).mul_left _
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun ξ => (hin ξ).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun ξ => tsum_nonneg fun ζ => hnn ⟨ξ, ζ⟩) (fun ξ => ?_)
    ((summable_norm_slotTerm fam hS hd Cχ hC hCpos L base roots tt κ τ).mul_right (∏ j, Mh j))
  rw [(hin ξ).tsum_eq]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun j _ => tsum_nonneg fun l => H.w_nn j _ l) fun j _ => hMh j _) (norm_nonneg _)

end WaveTurbulence.Represents
