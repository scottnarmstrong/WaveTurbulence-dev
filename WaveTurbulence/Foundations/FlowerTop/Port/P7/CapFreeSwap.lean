/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeKernel
/-! FLOWER-P7: integrability and the interchange of the decoration sum with the root-time integral. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

theorem norm_rootPhaseS {d : ℕ} (L γ δ : ℝ) (k : Mom d) (s : Fin 2 → ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) :
    ‖rootPhaseS L γ δ k s n‖ = 1 := by
  unfold rootPhaseS
  rw [norm_prod]
  exact Finset.prod_eq_one fun j _ => Complex.norm_exp_ofReal_mul_I _

theorem volume_rootDom_le (p : ℕ) (t : ℝ) : (volume : Measure (Fin 2 → ℝ)).real (rootDom p t) ≤ 1 := by
  have hsub : rootDom p t ⊆ Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (p : ℝ) (p + 1) := fun s hs j _ =>
    ⟨(hs j).1, (hs j).2.1⟩
  have h := measureReal_mono hsub (by
    rw [volume_pi_pi]; simp)
  refine h.trans (le_of_eq ?_)
  rw [measureReal_def, volume_pi_pi]
  simp

theorem measurableSet_rootDom (p : ℕ) (t : ℝ) : MeasurableSet (rootDom p t) := by
  unfold rootDom
  measurability

/-- The integrand over the root times, for a fixed decoration of the six trees. -/
noncomputable def gfun (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) (s : Fin 2 → ℝ) : ℂ :=
  (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s (fun c => κ' (GNode.root LG.garden.tree c)) *
    kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k κ') s

theorem gfun_eq (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) (s : Fin 2 → ℝ) :
    gfun L γ δ F LG p t k κ' s =
      ((epsDec LG.garden κ' : ℂ) * ∏ ℓ ∈ inputLeaves LG.garden,
        (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ' ℓ.toNode) : ℂ)) *
        ∫ σ : GBranch LG.garden.tree → ℝ, capF L γ δ LG hsig p hp t k κ' (extendCapS LG.garden.tree s σ) := by
  rw [inner_capF]
  unfold gfun kgTerm
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    simp only [Complex.ofReal_one, mul_one]
    ring
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]

theorem integrable_gfun (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    Integrable (gfun L γ δ F LG p t k κ') := by
  have h := (integrable_capF_prod L γ δ LG hsig p hp t k κ').integral_prod_left.const_mul
    ((epsDec LG.garden κ' : ℂ) * ∏ ℓ ∈ inputLeaves LG.garden,
        (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ' ℓ.toNode) : ℂ))
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [gfun_eq L γ δ F LG hsig p hp t k κ' s]

theorem norm_gfun_le (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) (s : Fin 2 → ℝ) :
    ‖gfun L γ δ F LG p t k κ' s‖ ≤ (rootDom p t).indicator (fun _ =>
      (volume : Measure ({b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ)).real
        (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) *
        kgBound L F LG k κ') s := by
  unfold gfun
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, norm_mul, norm_rootPhaseS, one_mul]
    exact norm_kgTerm_le L γ δ F LG _ (fun _ => none) k κ'
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]

end WaveTurbulence.FlowerP7
