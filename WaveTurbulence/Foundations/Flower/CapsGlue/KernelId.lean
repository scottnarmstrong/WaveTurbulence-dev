/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Kernel
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapKernel
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapPhase
/-! # A3a CAPS-GLUE: the time integral, the summand and the kernel of an n-ary glue factor -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset MeasureTheory WaveTurbulence.FlowerP7

variable {m w d : ℕ} {a : Fin m → ℕ}

theorem integrand_glueN (L γ δ : ℝ) (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (up : ∀ c, GBranch (LA c).garden.tree → ℝ) (fix : ∀ c, GBranch (LA c).garden.tree → Option ℝ)
    (off : ∀ c, Finset (GBranch (LA c).garden.tree)) (k : Mom d)
    (κ : ∀ c, GNode (LA c).garden.tree → (Fin d → ℤ))
    (τ : {b : GBranch (glueL σ LA).garden.tree //
      gBr σ (fun c => (LA c).garden.tree) fix b = none} → ℝ) :
    (kDomainFix (glueL σ LA) (gBr σ (fun c => (LA c).garden.tree) up)
        (gBr σ (fun c => (LA c).garden.tree) fix)).indicator
      (phaseProdOff L γ δ (glueL σ LA).garden (gOff σ (fun c => (LA c).garden.tree) off)
        (cosetDecoration (glueL σ LA).garden L k (gLabelN σ (fun c => (LA c).garden) κ)))
      ((glueL σ LA).garden.extendFix (gBr σ (fun c => (LA c).garden.tree) fix) τ) =
    ∏ c, (kDomainFix (LA c) (up c) (fix c)).indicator
      (phaseProdOff L γ δ (LA c).garden (off c) (cosetDecoration (LA c).garden L k (κ c)))
      ((LA c).garden.extendFix (fix c) (fun x => τ (freeEquivN σ (fun c => (LA c).garden.tree) fix ⟨c, x⟩))) := by
  rw [extendFix_glueN σ (fun c => (LA c).garden) fix τ]
  set τ' : ∀ c, GBranch (LA c).garden.tree → ℝ := fun c => (LA c).garden.extendFix (fix c)
    (fun x => τ (freeEquivN σ (fun c => (LA c).garden.tree) fix ⟨c, x⟩)) with hτ'
  by_cases h : ∀ c, τ' c ∈ kDomainFix (LA c) (up c) (fix c)
  · rw [Set.indicator_of_mem ((glueN_domain_iff σ LA up fix τ').2 h)]
    rw [phaseProd_glueN L γ δ σ (fun c => (LA c).garden) off k κ τ']
    exact Finset.prod_congr rfl fun c _ => (Set.indicator_of_mem (h c) _).symm
  · push_neg at h
    obtain ⟨c, hc⟩ := h
    rw [Set.indicator_of_notMem (fun h' => hc ((glueN_domain_iff σ LA up fix τ').1 h' c))]
    exact (Finset.prod_eq_zero (Finset.mem_univ c) (Set.indicator_of_notMem hc _)).symm

theorem integral_glueN (L γ δ : ℝ) (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (up : ∀ c, GBranch (LA c).garden.tree → ℝ) (fix : ∀ c, GBranch (LA c).garden.tree → Option ℝ)
    (off : ∀ c, Finset (GBranch (LA c).garden.tree)) (k : Mom d)
    (κ : ∀ c, GNode (LA c).garden.tree → (Fin d → ℤ)) :
    (∫ τ : {b : GBranch (glueL σ LA).garden.tree //
        gBr σ (fun c => (LA c).garden.tree) fix b = none} → ℝ,
      (kDomainFix (glueL σ LA) (gBr σ (fun c => (LA c).garden.tree) up)
          (gBr σ (fun c => (LA c).garden.tree) fix)).indicator
        (phaseProdOff L γ δ (glueL σ LA).garden (gOff σ (fun c => (LA c).garden.tree) off)
          (cosetDecoration (glueL σ LA).garden L k (gLabelN σ (fun c => (LA c).garden) κ)))
        ((glueL σ LA).garden.extendFix (gBr σ (fun c => (LA c).garden.tree) fix) τ)) =
    ∏ c, ∫ τ : {x : GBranch (LA c).garden.tree // fix c x = none} → ℝ,
      (kDomainFix (LA c) (up c) (fix c)).indicator
        (phaseProdOff L γ δ (LA c).garden (off c) (cosetDecoration (LA c).garden L k (κ c)))
        ((LA c).garden.extendFix (fix c) τ) := by
  rw [integral_equiv_pi (freeEquivN σ (fun c => (LA c).garden.tree) fix)]
  simp_rw [integrand_glueN L γ δ σ LA up fix off k κ]
  simp only [Equiv.symm_apply_apply]
  exact integral_sigma_pi_prod (fun c => {x : GBranch (LA c).garden.tree // fix c x = none})
    (fun c y => (kDomainFix (LA c) (up c) (fix c)).indicator
        (phaseProdOff L γ δ (LA c).garden (off c) (cosetDecoration (LA c).garden L k (κ c)))
        ((LA c).garden.extendFix (fix c) y))

theorem kgTerm_glueN (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w)
    (LA : ∀ c, LayeredGarden (a c)) (fix : ∀ c, GBranch (LA c).garden.tree → Option ℝ)
    (off : ∀ c, Finset (GBranch (LA c).garden.tree)) (wt : ∀ c, (GNode (LA c).garden.tree → Mom d) → ℝ)
    (up : ∀ c, GBranch (LA c).garden.tree → ℝ) (k : Mom d)
    (κ : ∀ c, GNode (LA c).garden.tree → (Fin d → ℤ)) :
    kgTerm L γ δ F (glueL σ LA) (gBr σ (fun c => (LA c).garden.tree) fix)
        (gOff σ (fun c => (LA c).garden.tree) off) (gWt σ (fun c => (LA c).garden.tree) wt)
        (gBr σ (fun c => (LA c).garden.tree) up) k (gLabelN σ (fun c => (LA c).garden) κ) =
      ∏ c, kgTerm L γ δ F (LA c) (fix c) (off c) (wt c) (up c) k (κ c) := by
  unfold kgTerm
  rw [integral_glueN L γ δ σ LA up fix off k κ, inputProd_glueN L F σ LA k κ,
    epsDec_glueN σ (fun c => (LA c).garden) κ]
  simp only [Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 3
  unfold gWt
  simp only [gLabelN_apply, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 3
  funext x
  rw [coset_glueN]

/-- **The n-ary glued kernel factors** (general `fix`, `off`, `wt`, `up`). -/
theorem kernelKgen_glueN (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w)
    (LA : ∀ c, LayeredGarden (a c)) (fix : ∀ c, GBranch (LA c).garden.tree → Option ℝ)
    (off : ∀ c, Finset (GBranch (LA c).garden.tree)) (wt : ∀ c, (GNode (LA c).garden.tree → Mom d) → ℝ)
    (up : ∀ c, GBranch (LA c).garden.tree → ℝ) (k : Mom d)
    (nA : ∀ c, Fin (a c) → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hs : ∀ c, Summable fun κ : GenDecoration (LA c).garden d (nA c) nfl =>
      kgTerm L γ δ F (LA c) (fix c) (off c) (wt c) (up c) k κ.1) :
    kernelKgen L γ δ F (glueL σ LA) (gBr σ (fun c => (LA c).garden.tree) fix)
        (gOff σ (fun c => (LA c).garden.tree) off) (gWt σ (fun c => (LA c).garden.tree) wt)
        (gBr σ (fun c => (LA c).garden.tree) up) k (gRootN σ nA) nfl =
      ∏ c, kernelKgen L γ δ F (LA c) (fix c) (off c) (wt c) (up c) k (nA c) nfl := by
  rw [kernelKgen_eq_tsum]
  simp_rw [kernelKgen_eq_tsum]
  have hlhs : ∑' κ : GenDecoration (glueL σ LA).garden d (gRootN σ nA) nfl,
      kgTerm L γ δ F (glueL σ LA) (gBr σ (fun c => (LA c).garden.tree) fix)
        (gOff σ (fun c => (LA c).garden.tree) off) (gWt σ (fun c => (LA c).garden.tree) wt)
        (gBr σ (fun c => (LA c).garden.tree) up) k κ.1 =
      ∏ c, ∑' κ : GenDecoration (LA c).garden d (nA c) nfl,
        kgTerm L γ δ F (LA c) (fix c) (off c) (wt c) (up c) k κ.1 := by
    rw [← (tsum_pi_prod m (fun c => GenDecoration (LA c).garden d (nA c) nfl)
      (fun c κ => kgTerm L γ δ F (LA c) (fix c) (off c) (wt c) (up c) k κ.1) fun c => (hs c).norm).2,
      ← (glueDecEquivN σ (fun c => (LA c).garden) nA nfl).symm.tsum_eq]
    refine tsum_congr fun z => ?_
    have : ((glueDecEquivN σ (fun c => (LA c).garden) nA nfl).symm z).1 =
        gLabelN σ (fun c => (LA c).garden) fun c => (z c).1 := rfl
    rw [this, kgTerm_glueN]
  rw [hlhs, glueN_order, glueN_zeta, ← Finset.prod_pow_eq_pow_sum]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

end WaveTurbulence.Flower.CapsGlue
