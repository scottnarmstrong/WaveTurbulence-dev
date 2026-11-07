/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeDomain
/-! FLOWER-P7: the time integral of the cap with free roots is the integral over the two root times of the root
phase times the time integral of the six trees with the caps `s_{j(c)}` (Fubini over the product
`(Fin 2 → ℝ) × (GBranch T → ℝ) ≃ᵐ (GBranch (capTree T) → ℝ)`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- All branching nodes of a garden are free when nothing is designated. -/
def freeEquivAll {w : ℕ} (T : Fin w → TTree) :
    GBranch T ≃ {b : GBranch T // (fun _ : GBranch T => (none : Option ℝ)) b = none} where
  toFun b := ⟨b, rfl⟩
  invFun b := b.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem extendFix_none_all {w : ℕ} (G : Garden w) (σ : GBranch G.tree → ℝ) :
    G.extendFix (fun _ => none) (fun b' => σ ((freeEquivAll G.tree).symm b')) = σ := by
  funext b
  rw [extendFix_none _ _ _ _ rfl]
  rfl

theorem measurableSet_kDomainFix_none {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) :
    MeasurableSet (kDomainFix LG up (fun _ => none)) := by
  unfold kDomainFix
  simp only [true_implies, or_self, forall_const]
  measurability

theorem continuous_phaseProdOff_empty {w d : ℕ} (L γ δ : ℝ) (G : Garden w) (k : GNode G.tree → Mom d) :
    Continuous (phaseProdOff L γ δ G ∅ k) := by
  unfold phaseProdOff
  simp only [Finset.notMem_empty, if_false]
  fun_prop

/-- The measurable equivalence between the pair (root times, six-tree times) and the times of the cap. -/
noncomputable def capTimeEquiv (T : Fin (2 * 3) → TTree) :
    ((Fin 2 → ℝ) × (GBranch T → ℝ)) ≃ᵐ (GBranch (capTree T) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ GBranch T => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : GBranch (capTree T) => ℝ) (capBranchEquiv T))

theorem capTimeEquiv_apply (T : Fin (2 * 3) → TTree) (x : (Fin 2 → ℝ) × (GBranch T → ℝ)) :
    capTimeEquiv T x = extendCapS T x.1 x.2 := by
  funext b
  obtain ⟨y, rfl⟩ := (capBranchEquiv T).surjective b
  simp only [capTimeEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply, extendCapS, Equiv.symm_apply_apply]
  rcases y with j | a <;> rfl

theorem capLayered_layer_le_p (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (b : GBranch (capTree LG.garden.tree)) :
    (capLayered LG hsig p hp).layer b.toNode ≤ p := by
  obtain ⟨y, rfl⟩ := (capBranchEquiv LG.garden.tree).surjective b
  rcases y with j | a
  · rw [capBranchEquiv_inl, capLayered_layer_root]
  · rw [capBranchEquiv_inr, liftBranch_toNode, capLayered_layer_lift]
    exact hp _

/-- The integrand over all times of the cap. -/
noncomputable def capF (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    (GBranch (capTree LG.garden.tree) → ℝ) → ℂ :=
  (kDomainFix (capLayered LG hsig p hp) (fun _ => t) (fun _ => none)).indicator
    (phaseProdOff L γ δ (capGarden LG.garden hsig) ∅
      (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ')))

theorem integrable_capF (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    Integrable (capF L γ δ LG hsig p hp t k κ') := by
  set Box : Set (GBranch (capTree LG.garden.tree) → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) (p + 1) with hBox
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  have hI : Integrable (Box.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBc.measure_lt_top.ne)
  refine Integrable.mono' hI ?_ (Filter.Eventually.of_forall fun τ => ?_)
  · exact ((continuous_phaseProdOff_empty L γ δ (capGarden LG.garden hsig)
      (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ'))).aestronglyMeasurable.indicator
      (measurableSet_kDomainFix_none _ _))
  · by_cases hD : τ ∈ kDomainFix (capLayered LG hsig p hp) (fun _ => t) (fun _ => none)
    · have hτ : τ ∈ Box := fun b _ => by
        have h := (hD b).1 rfl
        have hl := capLayered_layer_le_p LG hsig p hp b
        have hl' : ((capLayered LG hsig p hp).layer b.toNode : ℝ) ≤ p := by exact_mod_cast hl
        exact ⟨h.2.2.1.le, by linarith [h.2.1]⟩
      unfold capF
      rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
      simp only [phaseProdOff, norm_prod, Finset.notMem_empty, ite_false]
      refine le_of_eq (Finset.prod_eq_one fun b _ => ?_)
      exact Complex.norm_exp_ofReal_mul_I _
    · unfold capF
      rw [Set.indicator_of_notMem hD, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem integral_capF_prod (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    ∫ τ, capF L γ δ LG hsig p hp t k κ' τ =
      ∫ s : Fin 2 → ℝ, ∫ σ : GBranch LG.garden.tree → ℝ,
        capF L γ δ LG hsig p hp t k κ' (extendCapS LG.garden.tree s σ) := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ GBranch LG.garden.tree => ℝ)
  have h2 := measurePreserving_piCongrLeft (fun _ : GBranch (capTree LG.garden.tree) => (volume : Measure ℝ))
    (capBranchEquiv LG.garden.tree)
  have hmp : MeasurePreserving (capTimeEquiv LG.garden.tree) volume volume := h2.comp h1
  have hint := (hmp.integrable_comp_emb (capTimeEquiv LG.garden.tree).measurableEmbedding).2
    (integrable_capF L γ δ LG hsig p hp t k κ')
  rw [← hmp.integral_comp' (f := capTimeEquiv LG.garden.tree) (capF L γ δ LG hsig p hp t k κ')]
  simp only [capTimeEquiv_apply]
  rw [show (volume : Measure ((Fin 2 → ℝ) × (GBranch LG.garden.tree → ℝ))) =
    (volume : Measure (Fin 2 → ℝ)).prod (volume : Measure (GBranch LG.garden.tree → ℝ)) from rfl]
  have hint' : Integrable (fun x : (Fin 2 → ℝ) × (GBranch LG.garden.tree → ℝ) =>
      capF L γ δ LG hsig p hp t k κ' (extendCapS LG.garden.tree x.1 x.2))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure (GBranch LG.garden.tree → ℝ))) := by
    have h := hint
    simp only [Function.comp_def, capTimeEquiv_apply] at h
    exact h
  exact integral_prod _ hint'

theorem capF_extend (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ))
    (s : Fin 2 → ℝ) (σ : GBranch LG.garden.tree → ℝ) :
    capF L γ δ LG hsig p hp t k κ' (extendCapS LG.garden.tree s σ) =
      (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s (fun c => κ' (GNode.root LG.garden.tree c))) s *
        (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
          (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ')) σ := by
  unfold capF
  by_cases hs : s ∈ rootDom p t
  · by_cases hσ : σ ∈ kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)
    · rw [Set.indicator_of_mem ((domain_capS LG hsig p hp t s σ).2 ⟨hs, hσ⟩), Set.indicator_of_mem hs,
        Set.indicator_of_mem hσ, phaseProd_capS]
    · rw [Set.indicator_of_notMem (fun h => hσ ((domain_capS LG hsig p hp t s σ).1 h).2),
        Set.indicator_of_notMem hσ, mul_zero]
  · rw [Set.indicator_of_notMem (fun h => hs ((domain_capS LG hsig p hp t s σ).1 h).1),
      Set.indicator_of_notMem hs, zero_mul]

/-- **The time integral of the cap with free roots.** -/
theorem integral_cap_free (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    (∫ τ : {b : GBranch (capTree LG.garden.tree) // (fun _ : GBranch (capTree LG.garden.tree) => (none : Option ℝ)) b = none} → ℝ,
        (kDomainFix (capLayered LG hsig p hp) (fun _ => t) (fun _ => none)).indicator
          (phaseProdOff L γ δ (capGarden LG.garden hsig) ∅
            (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ')))
          ((capGarden LG.garden hsig).extendFix (fun _ => none) τ)) =
      ∫ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s (fun c => κ' (GNode.root LG.garden.tree c)) *
        ∫ σ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
          (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
            (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ'))
            (LG.garden.extendFix (fun _ => none) σ)) s := by
  rw [integral_equiv_pi (freeEquivAll (capTree LG.garden.tree))
    (fun τ => (kDomainFix (capLayered LG hsig p hp) (fun _ => t) (fun _ => none)).indicator
      (phaseProdOff L γ δ (capGarden LG.garden hsig) ∅
        (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ')))
      ((capGarden LG.garden hsig).extendFix (fun _ => none) τ))]
  have h1 : ∀ σ : GBranch (capTree LG.garden.tree) → ℝ,
      (kDomainFix (capLayered LG hsig p hp) (fun _ => t) (fun _ => none)).indicator
        (phaseProdOff L γ δ (capGarden LG.garden hsig) ∅
          (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ')))
        ((capGarden LG.garden hsig).extendFix (fun _ => none) (fun b' => σ ((freeEquivAll (capTree LG.garden.tree)).symm b'))) =
      capF L γ δ LG hsig p hp t k κ' σ := by
    intro σ
    rw [extendFix_none_all (capGarden LG.garden hsig)]
    rfl
  simp only [h1]
  rw [integral_capF_prod]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [capF_extend]
  rw [integral_const_mul]
  have h2 : ∀ (G : (GBranch LG.garden.tree → ℝ) → ℂ),
      ∫ σ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
        G (LG.garden.extendFix (fun _ => none) σ) = ∫ σ : GBranch LG.garden.tree → ℝ, G σ := by
    intro G
    rw [integral_equiv_pi (freeEquivAll LG.garden.tree) (fun σ => G (LG.garden.extendFix (fun _ => none) σ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only
    rw [extendFix_none_all]
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs,
      h2 (fun σ => (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
        (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ')) σ)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]

theorem integrable_capF_prod (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    Integrable (fun x : (Fin 2 → ℝ) × (GBranch LG.garden.tree → ℝ) =>
      capF L γ δ LG hsig p hp t k κ' (extendCapS LG.garden.tree x.1 x.2))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure (GBranch LG.garden.tree → ℝ))) := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ GBranch LG.garden.tree => ℝ)
  have h2 := measurePreserving_piCongrLeft (fun _ : GBranch (capTree LG.garden.tree) => (volume : Measure ℝ))
    (capBranchEquiv LG.garden.tree)
  have hmp : MeasurePreserving (capTimeEquiv LG.garden.tree) volume volume := h2.comp h1
  have hint := (hmp.integrable_comp_emb (capTimeEquiv LG.garden.tree).measurableEmbedding).2
    (integrable_capF L γ δ LG hsig p hp t k κ')
  have h := hint
  simp only [Function.comp_def, capTimeEquiv_apply] at h
  exact h

/-- The inner integral over the six-tree times of the cap integrand. -/
theorem inner_capF (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ))
    (s : Fin 2 → ℝ) :
    ∫ σ : GBranch LG.garden.tree → ℝ, capF L γ δ LG hsig p hp t k κ' (extendCapS LG.garden.tree s σ) =
      (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s (fun c => κ' (GNode.root LG.garden.tree c)) *
        ∫ σ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
          (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
            (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ'))
            (LG.garden.extendFix (fun _ => none) σ)) s := by
  simp only [capF_extend]
  rw [integral_const_mul]
  have h2 : ∀ (G : (GBranch LG.garden.tree → ℝ) → ℂ),
      ∫ σ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
        G (LG.garden.extendFix (fun _ => none) σ) = ∫ σ : GBranch LG.garden.tree → ℝ, G σ := by
    intro G
    rw [integral_equiv_pi (freeEquivAll LG.garden.tree) (fun σ => G (LG.garden.extendFix (fun _ => none) σ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only
    rw [extendFix_none_all]
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs,
      h2 (fun σ => (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
        (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ')) σ)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]

end WaveTurbulence.FlowerP7
