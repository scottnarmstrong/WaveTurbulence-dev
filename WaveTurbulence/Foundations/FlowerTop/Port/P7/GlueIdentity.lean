/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueKernel
/-! FLOWER-P7: the summand `kgTerm` and the kernel `kernelKgen` of a glued layered garden factor
(no designated nodes). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {a b w d : ℕ}

/-- All branching nodes are free when nothing is designated. -/
def freeEquivAny {n : ℕ} (T : Fin n → TTree) :
    GBranch T ≃ {b : GBranch T // (fun _ : GBranch T => (none : Option ℝ)) b = none} where
  toFun b := ⟨b, rfl⟩
  invFun b := b.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem extendFix_none_any {n : ℕ} (G : Garden n) (σ : GBranch G.tree → ℝ) :
    G.extendFix (fun _ => none) (fun b' => σ ((freeEquivAny G.tree).symm b')) = σ := by
  funext b
  rw [extendFix_none _ _ _ _ rfl]
  rfl

/-- The time integral of a glued garden is the product of the time integrals. -/
theorem integral_glue (L γ δ : ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (upA : GBranch LA.garden.tree → ℝ) (upB : GBranch LB.garden.tree → ℝ) (k : Mom d)
    (κA : GNode LA.garden.tree → (Fin d → ℤ)) (κB : GNode LB.garden.tree → (Fin d → ℤ)) :
    (∫ τ : {br : GBranch (glueLayered σ LA LB).garden.tree //
          (fun _ : GBranch (glueLayered σ LA LB).garden.tree => (none : Option ℝ)) br = none} → ℝ,
        (kDomainFix (glueLayered σ LA LB)
          (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br))
          (fun _ => none)).indicator
          (phaseProdOff L γ δ (glueLayered σ LA LB).garden ∅
            (cosetDecoration (glueLayered σ LA LB).garden L k (gLabel σ LA.garden LB.garden κA κB)))
          ((glueLayered σ LA LB).garden.extendFix (fun _ => none) τ)) =
      (∫ τ : {br : GBranch LA.garden.tree // (fun _ : GBranch LA.garden.tree => (none : Option ℝ)) br = none} → ℝ,
        (kDomainFix LA upA (fun _ => none)).indicator
          (phaseProdOff L γ δ LA.garden ∅ (cosetDecoration LA.garden L k κA))
          (LA.garden.extendFix (fun _ => none) τ)) *
      (∫ τ : {br : GBranch LB.garden.tree // (fun _ : GBranch LB.garden.tree => (none : Option ℝ)) br = none} → ℝ,
        (kDomainFix LB upB (fun _ => none)).indicator
          (phaseProdOff L γ δ LB.garden ∅ (cosetDecoration LB.garden L k κB))
          (LB.garden.extendFix (fun _ => none) τ)) := by
  rw [integral_equiv_pi (freeEquivAny (glueLayered σ LA LB).garden.tree)
      (fun τ => (kDomainFix (glueLayered σ LA LB)
          (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br))
          (fun _ => none)).indicator
          (phaseProdOff L γ δ (glueLayered σ LA LB).garden ∅
            (cosetDecoration (glueLayered σ LA LB).garden L k (gLabel σ LA.garden LB.garden κA κB)))
          ((glueLayered σ LA LB).garden.extendFix (fun _ => none) τ)),
    integral_equiv_pi (freeEquivAny LA.garden.tree)
      (fun τ => (kDomainFix LA upA (fun _ => none)).indicator
          (phaseProdOff L γ δ LA.garden ∅ (cosetDecoration LA.garden L k κA))
          (LA.garden.extendFix (fun _ => none) τ)),
    integral_equiv_pi (freeEquivAny LB.garden.tree)
      (fun τ => (kDomainFix LB upB (fun _ => none)).indicator
          (phaseProdOff L γ δ LB.garden ∅ (cosetDecoration LB.garden L k κB))
          (LB.garden.extendFix (fun _ => none) τ))]
  simp only [extendFix_none_any]
  rw [integral_equiv_pi (glueBranch σ LA.garden.tree LB.garden.tree)
    (fun τ => (kDomainFix (glueLayered σ LA LB)
          (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br))
          (fun _ => none)).indicator
          (phaseProdOff L γ δ (glueLayered σ LA LB).garden ∅
            (cosetDecoration (glueLayered σ LA LB).garden L k (gLabel σ LA.garden LB.garden κA κB))) τ),
    ← integral_sum_pi_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  have hρ : (fun b' => ρ ((glueBranch σ LA.garden.tree LB.garden.tree).symm b')) =
      gTime σ LA.garden.tree LB.garden.tree (fun x => ρ (.inl x)) (fun x => ρ (.inr x)) := by
    funext b'
    obtain ⟨y, rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective b'
    rcases y with x | x <;> simp
  simp only
  rw [hρ]
  by_cases hA : (fun x => ρ (.inl x)) ∈ kDomainFix LA upA (fun _ => none)
  · by_cases hB : (fun x => ρ (.inr x)) ∈ kDomainFix LB upB (fun _ => none)
    · rw [Set.indicator_of_mem ((glue_domain_iff σ LA LB upA upB _ _).2 ⟨hA, hB⟩),
        Set.indicator_of_mem hA, Set.indicator_of_mem hB, phaseProd_glue]
    · rw [Set.indicator_of_notMem (fun h => hB ((glue_domain_iff σ LA LB upA upB _ _).1 h).2),
        Set.indicator_of_notMem hB, mul_zero]
  · rw [Set.indicator_of_notMem (fun h => hA ((glue_domain_iff σ LA LB upA upB _ _).1 h).1),
      Set.indicator_of_notMem hA, zero_mul]

/-- The summand of the glued kernel is the product of the summands. -/
theorem kgTerm_glue (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a)
    (LB : LayeredGarden b) (upA : GBranch LA.garden.tree → ℝ) (upB : GBranch LB.garden.tree → ℝ) (k : Mom d)
    (κA : GNode LA.garden.tree → (Fin d → ℤ)) (κB : GNode LB.garden.tree → (Fin d → ℤ)) :
    kgTerm L γ δ F (glueLayered σ LA LB) (fun _ => none) ∅ (fun _ => 1)
        (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br)) k
        (gLabel σ LA.garden LB.garden κA κB) =
      kgTerm L γ δ F LA (fun _ => none) ∅ (fun _ => 1) upA k κA *
        kgTerm L γ δ F LB (fun _ => none) ∅ (fun _ => 1) upB k κB := by
  unfold kgTerm
  rw [integral_glue L γ δ σ LA LB upA upB k κA κB, inputProd_glue L F σ LA LB k κA κB,
    epsDec_glue σ LA.garden LB.garden κA κB]
  simp only [Complex.ofReal_one, Complex.ofReal_mul, mul_one]
  ring

/-- **The glued kernel factors** (no designated nodes). -/
theorem kernelKgen_glue (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a)
    (LB : LayeredGarden b) (upA : GBranch LA.garden.tree → ℝ) (upB : GBranch LB.garden.tree → ℝ) (k : Mom d)
    (nA : Fin a → (Fin d → ℤ)) (nB : Fin b → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hsA : Summable fun κ : GenDecoration LA.garden d nA nfl =>
      kgTerm L γ δ F LA (fun _ => none) ∅ (fun _ => 1) upA k κ.1)
    (hsB : Summable fun κ : GenDecoration LB.garden d nB nfl =>
      kgTerm L γ δ F LB (fun _ => none) ∅ (fun _ => 1) upB k κ.1) :
    kernelKgen L γ δ F (glueLayered σ LA LB) (fun _ => none) ∅ (fun _ => 1)
        (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br)) k
        (gRoot σ nA nB) nfl =
      kernelKgen L γ δ F LA (fun _ => none) ∅ (fun _ => 1) upA k nA nfl *
        kernelKgen L γ δ F LB (fun _ => none) ∅ (fun _ => 1) upB k nB nfl := by
  rw [kernelKgen_eq_tsum, kernelKgen_eq_tsum, kernelKgen_eq_tsum]
  have hlhs : ∑' κ : GenDecoration (glueLayered σ LA LB).garden d (gRoot σ nA nB) nfl,
      kgTerm L γ δ F (glueLayered σ LA LB) (fun _ => none) ∅ (fun _ => 1)
        (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br)) k κ.1 =
      (∑' κ : GenDecoration LA.garden d nA nfl, kgTerm L γ δ F LA (fun _ => none) ∅ (fun _ => 1) upA k κ.1) *
        ∑' κ : GenDecoration LB.garden d nB nfl, kgTerm L γ δ F LB (fun _ => none) ∅ (fun _ => 1) upB k κ.1 := by
    rw [tsum_mul_tsum_of_summable_norm hsA.norm hsB.norm,
      ← (glueDecEquiv σ LA.garden LB.garden nA nB nfl).symm.tsum_eq]
    refine tsum_congr fun z => ?_
    have : ((glueDecEquiv σ LA.garden LB.garden nA nB nfl).symm z).1 =
        gLabel σ LA.garden LB.garden z.1.1 z.2.1 := rfl
    rw [this, kgTerm_glue]
  rw [hlhs, glue_order, glue_zeta]
  show (coupling d L γ δ : ℂ) ^ (LA.garden.order + LB.garden.order) * (LA.garden.zeta * LB.garden.zeta) * _ = _
  rw [pow_add]
  ring

end WaveTurbulence.FlowerP7
