/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation

/-! # Fubini for actual finite Fourier-cell mixtures over a product parameter measure -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset

variable {U V I : Type*} [MeasurableSpace U] [MeasurableSpace V] [Fintype I]
  (μ : Measure U) (ν : Measure V) [SFinite μ] [SFinite ν]

/-- Finite sums commute with the actual product integral under absolute
integrability of each original coefficient. -/
theorem integral_fintype_integral_eq_tsum_integral_prod
    (F : I → U × V → ℂ) (hi : ∀ i, Integrable (F i) (μ.prod ν)) :
    (∫ u, ∑ i, ∫ v, F i (u,v) ∂ν ∂μ) = ∑' i, ∫ p, F i p ∂μ.prod ν := by
  rw [integral_finsetSum _ (fun i _ => (hi i).integral_prod_left),tsum_fintype]
  apply sum_congr rfl
  intro i _
  exact (integral_prod _ (hi i)).symm

/-- Actual singular integration commutes with the outer parameter integral
for finite Fourier-cell mixtures. All analytic premises concern the
original jointly integrable coefficients, before any singular operator. -/
theorem singInt_integral_finiteCellMixture {d n : ℕ} (hd : 3 ≤ d)
    (J : Finset (Fin n)) (p q : I → Fin n → Mom d)
    (ξ η : I → U × V → Fin n → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U × V → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) (μ.prod ν)) :
    singInt J (fun x y => ∫ u, ∑ i, ∫ v, h i (u,v)*
      ∏ j, cellFn (p i j) (q i j) (ξ i (u,v) j) (η i (u,v) j) (x j) (y j) ∂ν ∂μ) =
      ∫ u, ∑ i, ∫ v, h i (u,v)*
        ∏ j, cellOp J j (p i j) (q i j) (ξ i (u,v) j) (η i (u,v) j) ∂ν ∂μ := by
  classical
  obtain ⟨M,hM,hb⟩ := exists_cellOp_bound hd
  have hprod (i : I) (k : ℕ) (x y : Fin n → Mom d) :
      StronglyMeasurable (fun uv => ∏ j, mixtureAppFactor J k (p i) (q i) (ξ i uv) (η i uv) x y j) :=
    Finset.stronglyMeasurable_fun_prod _ (fun j _ =>
      stronglyMeasurable_mixtureAppFactor hd J k (p i) (q i) (ξ i) (η i) (hξ i) (hη i) x y j)
  have hbound (i : I) (k : ℕ) (x y : Fin n → Mom d) (uv : U × V) :
      ‖∏ j, mixtureAppFactor J k (p i) (q i) (ξ i uv) (η i uv) x y j‖ ≤ M^n := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _j : Fin n, M := prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => norm_mixtureAppFactor_le hM hb J k (p i) (q i) (ξ i uv) (η i uv) x y j)
      _ = _ := by simp
  have hi' (i : I) (k : ℕ) (x y : Fin n → Mom d) :
      Integrable (fun uv => h i uv*∏ j,
        mixtureAppFactor J k (p i) (q i) (ξ i uv) (η i uv) x y j) (μ.prod ν) :=
    (hi i).mul_bdd (c := M^n) (hprod i k x y).aestronglyMeasurable
      (ae_of_all _ (hbound i k x y))
  have hexchange (k : ℕ) (x y : Fin n → Mom d) :=
    integral_fintype_integral_eq_tsum_integral_prod μ ν
      (fun i uv => h i uv*∏ j, mixtureAppFactor J k (p i) (q i) (ξ i uv) (η i uv) x y j)
      (fun i => hi' i k x y)
  have hleft : (fun (x y : Fin n → Mom d) => ∫ u, ∑ i, ∫ v, h i (u,v)*
      ∏ j, cellFn (p i j) (q i j) (ξ i (u,v) j) (η i (u,v) j) (x j) (y j) ∂ν ∂μ) =
      (fun (x y : Fin n → Mom d) => ∑' i, ∫ uv, h i uv*
        ∏ j, cellFn (p i j) (q i j) (ξ i uv j) (η i uv j) (x j) (y j) ∂μ.prod ν) := by
    funext x y
    have hj : ∀ j : Fin n, ¬(n ≤ j.val+0) := fun j => by omega
    simpa only [mixtureAppFactor,hj,ite_false] using hexchange 0 x y
  rw [hleft,singInt_countableCellMixture (μ.prod ν) hd J p q ξ η hξ hη h hsm hi (hasSum_fintype _).summable]
  have he := hexchange n (0:Fin n → Mom d) (0:Fin n → Mom d)
  simpa only [mixtureAppFactor,Nat.le_add_left,ite_true] using he.symm

end WaveTurbulence.RegAsymp
