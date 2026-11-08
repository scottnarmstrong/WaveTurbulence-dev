/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
/-! # A3a CAPS-GLUE: product formulas over a finite family of index types (integral and `tsum`) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CapsGlue
open MeasureTheory

/-- Currying `((Σ c, κ c) → ℝ) ≃ ∀ c, κ c → ℝ` preserves Lebesgue measure. -/
theorem measurePreserving_piCurry_real {m : ℕ} (κ : Fin m → Type) [∀ c, Fintype (κ c)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (c : Fin m) (_ : κ c) => ℝ))
      (volume : Measure ((Σ c, κ c) → ℝ)) (Measure.pi fun c => (volume : Measure (κ c → ℝ))) := by
  set e := MeasurableEquiv.piCurry (fun (c : Fin m) (_ : κ c) => ℝ) with he
  have key : Measure.map e.symm (Measure.pi fun c => (volume : Measure (κ c → ℝ))) =
      (volume : Measure ((Σ c, κ c) → ℝ)) := by
    refine (Measure.pi_eq (μ := fun _ : (Σ c, κ c) => (volume : Measure ℝ))
      (μ' := Measure.map e.symm (Measure.pi fun c => (volume : Measure (κ c → ℝ)))) ?_).symm
    intro s hs
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs)]
    have hpre : e.symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun c : Fin m => Set.univ.pi (fun j : κ c => s ⟨c, j⟩)) := by
      ext y
      simp [he, MeasurableEquiv.coe_piCurry_symm, Sigma.forall, Sigma.uncurry]
    rw [hpre, Measure.pi_pi]
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun c _ => Measure.pi_pi (fun _ : κ c => (volume : Measure ℝ)) _
  exact MeasurePreserving.symm e.symm ⟨e.symm.measurable, key⟩

/-- Product formula for integrals over a sigma-indexed function space. -/
theorem integral_sigma_pi_prod {m : ℕ} (κ : Fin m → Type) [∀ c, Fintype (κ c)]
    (Φ : ∀ c, (κ c → ℝ) → ℂ) :
    ∫ x : (Σ c, κ c) → ℝ, ∏ c, Φ c (fun j => x ⟨c, j⟩) = ∏ c, ∫ y : κ c → ℝ, Φ c y := by
  have hmp := measurePreserving_piCurry_real κ
  have := hmp.integral_comp' (f := MeasurableEquiv.piCurry (fun (c : Fin m) (_ : κ c) => ℝ))
    (fun y => ∏ c, Φ c (y c))
  rw [show (fun x : (Σ c, κ c) → ℝ => ∏ c, Φ c (fun j => x ⟨c, j⟩)) =
      fun x => (fun y : ∀ c, κ c → ℝ => ∏ c, Φ c (y c))
        (MeasurableEquiv.piCurry (fun (c : Fin m) (_ : κ c) => ℝ) x) from rfl, this]
  exact integral_fintype_prod_eq_prod (μ := fun c => (volume : Measure (κ c → ℝ))) Φ

/-- Product formula for `tsum` over a finite product of index types (all families absolutely summable). -/
theorem tsum_pi_prod : ∀ (m : ℕ) (D : Fin m → Type) (g : ∀ c, D c → ℂ)
    (_ : ∀ c, Summable fun x => ‖g c x‖),
    (Summable fun f : (∀ c, D c) => ‖∏ c, g c (f c)‖) ∧
      ∑' f : (∀ c, D c), ∏ c, g c (f c) = ∏ c, ∑' x, g c x
  | 0, D, g, _ => by
    haveI : Unique (∀ c : Fin 0, D c) := Pi.uniqueOfIsEmpty _
    refine ⟨Summable.of_finite, ?_⟩
    simp
  | m + 1, D, g, hg => by
    obtain ⟨hs, ht⟩ := tsum_pi_prod m (fun i => D i.succ) (fun i => g i.succ) fun i => hg i.succ
    set e := Fin.consEquiv D with he
    have hprod : ∀ z : D 0 × (∀ i : Fin m, D i.succ),
        ∏ c, g c (e z c) = g 0 z.1 * ∏ i : Fin m, g i.succ (z.2 i) := by
      intro z
      rw [Fin.prod_univ_succ]
      simp [he, Fin.consEquiv]
    have hsum : Summable fun z : D 0 × (∀ i : Fin m, D i.succ) =>
        ‖g 0 z.1 * ∏ i : Fin m, g i.succ (z.2 i)‖ := by
      have := (hg 0).mul_norm hs
      refine this.congr fun z => ?_
      simp [norm_mul]
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      refine hsum.congr fun z => ?_
      rw [Function.comp_apply, hprod]
    · rw [← e.tsum_eq]
      simp_rw [hprod]
      rw [← tsum_mul_tsum_of_summable_norm (hg 0) hs, ht, Fin.prod_univ_succ]

end WaveTurbulence.Flower.CapsGlue
