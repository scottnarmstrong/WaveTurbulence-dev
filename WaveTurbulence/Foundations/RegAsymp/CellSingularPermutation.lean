/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation

/-! # Pair-enumeration invariance for actual absolutely summable singular cell mixtures -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset

/-- A literal reindexing preserves the marked status and every local
singular cell operator, including its actual delta/PV choice. -/
theorem cellOp_equiv {d n m : ℕ} (e : Fin n ≃ Fin m) (J : Finset (Fin m))
    (j : Fin n) (p q ξ η : Mom d) :
    cellOp (J.preimage e e.injective.injOn) j p q ξ η = cellOp J (e j) p q ξ η := by
  simp only [cellOp,mem_preimage]

/-- The actual countable-cell singular integral does not depend on pair
enumeration. This derives the permutation from the convergent cell
representation, rather than assuming unrestricted principal-value Fubini. -/
theorem singInt_countableCellMixture_equiv
    {U I : Type*} [MeasurableSpace U] [Countable I]
    (ν : Measure U) [SFinite ν] {d n m : ℕ} (hd : 3 ≤ d)
    (e : Fin n ≃ Fin m) (J : Finset (Fin m))
    (p q : I → Fin m → Mom d) (ξ η : I → U → Fin m → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) :
    singInt (J.preimage e e.injective.injOn)
      (fun x y => ∑' i, ∫ u, h i u * ∏ j : Fin n,
        cellFn (p i (e j)) (q i (e j)) (ξ i u (e j)) (η i u (e j)) (x j) (y j) ∂ν) =
    singInt J (fun x y => ∑' i, ∫ u, h i u * ∏ j : Fin m,
      cellFn (p i j) (q i j) (ξ i u j) (η i u j) (x j) (y j) ∂ν) := by
  have hξ' (i : I) : Measurable (fun u => fun j : Fin n => ξ i u (e j)) :=
    Measurable.of_eval (fun j => (measurable_pi_apply (e j)).comp (hξ i))
  have hη' (i : I) : Measurable (fun u => fun j : Fin n => η i u (e j)) :=
    Measurable.of_eval (fun j => (measurable_pi_apply (e j)).comp (hη i))
  rw [singInt_countableCellMixture ν hd (J.preimage e e.injective.injOn)
    (fun i j => p i (e j)) (fun i j => q i (e j))
    (fun i u j => ξ i u (e j)) (fun i u j => η i u (e j)) hξ' hη' h hsm hi hsum,
    singInt_countableCellMixture ν hd J p q ξ η hξ hη h hsm hi hsum]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  apply ae_of_all
  intro u
  dsimp only
  congr 1
  simp_rw [cellOp_equiv]
  exact e.prod_comp (fun j => cellOp J j (p i j) (q i j) (ξ i u j) (η i u j))

end WaveTurbulence.RegAsymp
