/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeLayer
/-! FLOWER-P7: integrability in the root times of the six-tree kernels with free caps. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

theorem integrable_tsum_gfun (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (nroot : Fin (2 * 3) → (Fin d → ℤ)) (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) :
    Integrable (fun s => ∑' κ : GenDecoration LG.garden d nroot 0, gfun L γ δ F LG p t k κ.1 s) := by
  classical
  set C := (volume : Measure ({b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ)).real
    (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) with hC
  have hsB := summable_kgBound L F LG k nroot 0 (plain_hlone _ hplain) (fun ℓ _ => hF _)
  have hmeas := measurableSet_rootDom p t
  have hsum : ∀ s, Summable fun κ : GenDecoration LG.garden d nroot 0 => gfun L γ δ F LG p t k κ.1 s := by
    intro s
    refine Summable.of_norm_bounded (g := fun κ : GenDecoration LG.garden d nroot 0 =>
      (rootDom p t).indicator (fun _ => C * kgBound L F LG k κ.1) s) ?_ (fun κ => norm_gfun_le L γ δ F LG p t k κ.1 s)
    by_cases hs : s ∈ rootDom p t
    · simp only [Set.indicator_of_mem hs]
      exact hsB.mul_left C
    · simp only [Set.indicator_of_notMem hs]
      exact summable_zero
  have hae : AEStronglyMeasurable (fun s => ∑' κ : GenDecoration LG.garden d nroot 0, gfun L γ δ F LG p t k κ.1 s) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset (GenDecoration LG.garden d nroot 0))))
      (f := fun S s => ∑ κ ∈ S, gfun L γ δ F LG p t k κ.1 s) (fun S => ?_)
      (Filter.Eventually.of_forall fun s => (hsum s).hasSum)
    exact (integrable_finset_sum S fun κ _ => integrable_gfun L γ δ F LG hsig p hp t k κ.1).aestronglyMeasurable
  have hI : Integrable ((rootDom p t).indicator fun _ => C * ∑' κ : GenDecoration LG.garden d nroot 0, kgBound L F LG k κ.1) :=
    (integrable_indicator_iff hmeas).2 (integrableOn_const (volume_rootDom_lt_top p t).ne)
  refine Integrable.mono' hI hae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs]
    have h := tsum_of_norm_bounded (hsB.mul_left C).hasSum (f := fun κ : GenDecoration LG.garden d nroot 0 =>
      gfun L γ δ F LG p t k κ.1 s) (fun κ => by
        have := norm_gfun_le L γ δ F LG p t k κ.1 s
        rwa [Set.indicator_of_mem hs] at this)
    rwa [tsum_mul_left] at h
  · rw [Set.indicator_of_notMem hs]
    have h0 : ∀ κ : GenDecoration LG.garden d nroot 0, gfun L γ δ F LG p t k κ.1 s = 0 := fun κ => by
      unfold gfun; rw [Set.indicator_of_notMem hs]
    simp [h0]

end WaveTurbulence.FlowerP7
