/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapDomain
/-! FLOWER-P7: the summand of the general kernel `kernelKgen` and its factorisation across the cap. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

theorem extendFix_some {w : ℕ} (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) (b : GBranch G.tree) (v : ℝ) (h : fix b = some v) :
    G.extendFix fix τ b = v := by
  unfold Garden.extendFix
  split
  · rename_i v' hv'
    rw [h] at hv'
    exact (Option.some.inj hv').symm
  · rename_i hv'
    rw [h] at hv'
    exact absurd hv' (by simp)

theorem extendFix_none {w : ℕ} (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) (b : GBranch G.tree) (h : fix b = none) :
    G.extendFix fix τ b = τ ⟨b, h⟩ := by
  unfold Garden.extendFix
  split
  · rename_i v' hv'
    rw [h] at hv'
    exact absurd hv' (by simp)
  · rfl

/-- The free branching nodes of the pinned cap are the lifted ones. -/
noncomputable def freeEquivQ (T : Fin (2 * 3) → TTree) (t : ℝ) :
    GBranch T ≃ {b : GBranch (capTree T) // pinRoots (T := T) t b = none} :=
  Equiv.ofBijective (fun a => ⟨liftBranch a, pinRoots_lift t a⟩) (by
    constructor
    · intro a a' h
      exact liftBranch_injective (congrArg Subtype.val h)
    · rintro ⟨b, hb⟩
      have hne : b.1.2 ≠ [] := by
        intro h0
        have : pinRoots (T := T) t b = some t := by simp [pinRoots, h0]
        rw [this] at hb
        exact absurd hb (by simp)
      obtain ⟨a, ha⟩ := exists_liftBranch b hne
      exact ⟨a, Subtype.ext ha⟩)

/-- All branching nodes of a garden are free when nothing is designated. -/
def freeEquivG (T : Fin (2 * 3) → TTree) :
    GBranch T ≃ {b : GBranch T // (fun _ : GBranch T => (none : Option ℝ)) b = none} where
  toFun b := ⟨b, rfl⟩
  invFun b := b.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem extendFix_pin (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (t : ℝ)
    (σ : GBranch G.tree → ℝ) :
    (capGarden G hsig).extendFix (pinRoots (T := G.tree) t)
        (fun b' => σ ((freeEquivQ G.tree t).symm b')) = extendCap G.tree t σ := by
  funext b
  obtain ⟨y, rfl⟩ := (capBranchEquiv G.tree).surjective b
  rcases y with j | a
  · rw [capBranchEquiv_inl, extendFix_some _ _ _ _ t (pinRoots_root t j), extendCap_root]
  · rw [capBranchEquiv_inr, extendFix_none _ _ _ _ (pinRoots_lift t a), extendCap_lift]
    have : (freeEquivQ G.tree t).symm ⟨liftBranch a, pinRoots_lift t a⟩ = a := by
      rw [Equiv.symm_apply_eq]; rfl
    rw [this]

theorem extendFix_none_G (G : Garden (2 * 3)) (σ : GBranch G.tree → ℝ) :
    G.extendFix (fun _ => none) (fun b' => σ ((freeEquivG G.tree).symm b')) = σ := by
  funext b
  rw [extendFix_none _ _ _ _ rfl]
  rfl

/-- The time integral of the pinned cap is the root phase times the time integral of the six trees. -/
theorem integral_cap (L γ δ : ℝ) (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d) (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    (∫ τ : {b : GBranch (capTree LG.garden.tree) // pinRoots (T := LG.garden.tree) t b = none} → ℝ,
        (kDomainFix (capLayered LG hsig p hp) (fun _ => t) (pinRoots (T := LG.garden.tree) t)).indicator
          (phaseProdOff L γ δ (capGarden LG.garden hsig) ∅
            (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ')))
          ((capGarden LG.garden hsig).extendFix (pinRoots (T := LG.garden.tree) t) τ)) =
      rootPhase L γ δ k t (fun c => κ' (GNode.root LG.garden.tree c)) *
        ∫ τ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
          (kDomainFix LG (fun _ => t) (fun _ => none)).indicator
            (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ'))
            (LG.garden.extendFix (fun _ => none) τ) := by
  rw [integral_equiv_pi (freeEquivQ LG.garden.tree t)
      (fun τ => (kDomainFix (capLayered LG hsig p hp) (fun _ => t) (pinRoots (T := LG.garden.tree) t)).indicator
        (phaseProdOff L γ δ (capGarden LG.garden hsig) ∅
          (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ')))
        ((capGarden LG.garden hsig).extendFix (pinRoots (T := LG.garden.tree) t) τ)),
    integral_equiv_pi (freeEquivG LG.garden.tree)
      (fun τ => (kDomainFix LG (fun _ => t) (fun _ => none)).indicator
        (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ'))
        (LG.garden.extendFix (fun _ => none) τ)), ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only
  rw [extendFix_pin, extendFix_none_G]
  by_cases hσ : σ ∈ kDomainFix LG (fun _ => t) (fun _ => none)
  · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem ((domain_cap LG hsig p hp t σ).2 hσ),
      phaseProd_cap]
  · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (fun h => hσ ((domain_cap LG hsig p hp t σ).1 h)),
      mul_zero]

end WaveTurbulence.FlowerP7
