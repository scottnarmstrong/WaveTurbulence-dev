/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafLocalizationMass

/-!
# Exact finite-family leaf localization and its total coefficient

The product of smooth cell decompositions recovers the actual leaf
product. The full coefficient is a product of one-factor masses.
-/

public section
noncomputable section
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Tonelli for a finite number of independent nonnegative series. -/
theorem tsum_fin_product_ennreal {U : Type*} (n : ℕ) (a : Fin n → U → ℝ≥0∞) :
    (∑' c : Fin n → U, ∏ i, a i (c i)) = ∏ i, ∑' u, a i u := by
  induction n with
  | zero => simp
  | succ n ih =>
    let e : (Fin (n + 1) → U) ≃ U × (Fin n → U) :=
      { toFun := fun c => (c 0, Fin.tail c)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun c => Fin.cons_self_tail c
        right_inv := by intro p; simp }
    calc
      _ = ∑' p : U × (Fin n → U), ∏ i, a i ((Fin.cons p.1 p.2 : Fin (n + 1) → U) i) :=
        (e.symm.tsum_eq (fun c => ∏ i, a i (c i))).symm
      _ = ∑' u : U, ∑' c : Fin n → U, a 0 u * ∏ i, a i.succ (c i) := by
        rw [ENNReal.tsum_prod' (f := fun p : U × (Fin n → U) =>
          ∏ i, a i ((Fin.cons p.1 p.2 : Fin (n + 1) → U) i))]
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      _ = _ := by
        simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
        rw [Fin.prod_univ_succ]

/-- Every finite product of leaf inputs is the exact sum of its actual smooth cell products. -/
theorem hasSum_leafCell_product {d m : ℕ} (f : Fin m → Mom d → ℂ) (x : Fin m → Mom d) :
    HasSum (fun c : Fin m → Fin d → ℤ => ∏ i, leafCell (f i) (c i) (x i)) (∏ i, f i (x i)) := by
  classical
  let S := Fintype.piFinset (fun i : Fin m => ApproxNT.thetaSupport (x i))
  have hz (c : Fin m → Fin d → ℤ) (hc : c ∉ S) : ∏ i, leafCell (f i) (c i) (x i) = 0 := by
    have hn : ¬∀ i, c i ∈ ApproxNT.thetaSupport (x i) := by
      simpa only [S, Fintype.mem_piFinset] using hc
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (leafCell_eq_zero_of_notMem (f i) (x i) hi)
  have hs : HasSum (fun c : Fin m → Fin d → ℤ => ∏ i, leafCell (f i) (c i) (x i))
      (∑ c ∈ S, ∏ i, leafCell (f i) (c i) (x i)) := hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  dsimp only [S]
  rw [← Finset.prod_univ_sum (fun i => ApproxNT.thetaSupport (x i))
    (fun i c => leafCell (f i) c (x i))]
  apply Finset.prod_congr rfl
  intro i _
  simp_rw [leafCell]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, ApproxNT.sum_thetaMom, Complex.ofReal_one, mul_one]

/-- The total Fourier coefficient of all simultaneous leaf cells is exponential in the leaf count. -/
theorem tsum_prod_timeFourierNorm_leafCell_le {d m K M : ℕ} (f : Fin m → Mom d → ℂ)
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i, Fourier.spatialNorm K M (f i) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ, ∏ i,
      Fourier.timeFourierNorm 0 (fun x : Fin d → ℝ => leafCell (f i) (c i) (WithLp.toLp 2 x))) ≤
        ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m := by
  rw [tsum_fin_product_ennreal m (fun i c =>
    Fourier.timeFourierNorm 0 (fun x : Fin d → ℝ => leafCell (f i) c (WithLp.toLp 2 x)))]
  calc
    _ ≤ ∏ _i : Fin m, ENNReal.ofReal (leafLocalizationConstant d M * B) :=
      Finset.prod_le_prod (fun i _ => tsum_timeFourierNorm_leafCell_le hK hM hB (hf i))
    _ = _ := by simp

end WaveTurbulence.Incoh
