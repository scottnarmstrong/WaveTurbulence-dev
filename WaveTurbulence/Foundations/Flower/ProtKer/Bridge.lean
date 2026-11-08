/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub

/-! # D2a PROT-KER: the bridge `kernelProt = Stage1W.kernelLeavesW`, scaling and vanishing -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtDefs

/-- With `fix ≡ none` and no flower parent, the integrals over the free times agree termwise. -/
theorem kernelProt_term_none (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (x : GNode LG.garden.tree → Mom d)
    (hnf : ∀ b, ¬ LG.garden.IsFlowerParent b) :
    (∫ τ : {b : GBranch LG.garden.tree // (fun _ => (none : Option ℝ)) b = none} → ℝ,
        (kDomainFix LG up (fun _ => none) ∩
            {τ | ∀ b, LG.garden.IsLoneParent b → (fun _ => (none : Option ℝ)) b = none → s < τ b}).indicator
          (phaseProd L γ δ LG.garden x) (LG.garden.extendFix (fun _ => none) τ)) =
      phaseIntegral L γ δ LG.garden (kDomain LG up s) s x := by
  unfold phaseIntegral
  have hfree : ∀ b : GBranch LG.garden.tree,
      ¬ LG.garden.IsFlowerParent b ↔ (none : Option ℝ) = none :=
    fun b => ⟨fun _ => rfl, fun _ => hnf b⟩
  have key := FlowerP1.integral_subtype_congr (Pp := fun b => ¬ LG.garden.IsFlowerParent b)
    (Q := fun _ => (none : Option ℝ) = none) (fun b => hfree b)
    (fun σ => (kDomainFix LG up (fun _ => none) ∩
            {τ | ∀ b, LG.garden.IsLoneParent b → (fun _ => (none : Option ℝ)) b = none → s < τ b}).indicator
      (phaseProd L γ δ LG.garden x) (LG.garden.extendFix (fun _ => none) σ))
  refine key.symm.trans ?_
  show _ = ∫ τ : LG.garden.FreeBranch → ℝ, _
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have hext : LG.garden.extendFix (fun _ => none) (fun q => τ ⟨q.1, hnf q.1⟩) =
      LG.garden.extendTime s τ := by
    funext b
    simp [Garden.extendFix, Garden.extendTime, hnf b]
  beta_reduce
  rw [hext]
  have hdom : LG.garden.extendTime s τ ∈ kDomainFix LG up (fun _ => none) ∩
        {τ | ∀ b, LG.garden.IsLoneParent b → (fun _ => (none : Option ℝ)) b = none → s < τ b} ↔
      LG.garden.extendTime s τ ∈ kDomain LG up s := by
    constructor
    · rintro ⟨h, h'⟩ b
      obtain ⟨h1, h2, h3, h4⟩ := (h b).1 rfl
      exact ⟨h1, h2, h3, h4, fun b' hb' => (h b).2 b' hb' (Or.inl rfl), fun hl => h' b hl rfl⟩
    · intro h
      refine ⟨fun b => ⟨fun _ => ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.1⟩, fun b' hb' _ =>
        (h b).2.2.2.2.1 b' hb'⟩, fun b hl _ => (h b).2.2.2.2.2 hl⟩
  by_cases hmem : LG.garden.extendTime s τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hdom.2 hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h => hmem (hdom.1 h))]

theorem kernelProtBridge : KernelProtBridge := by
  intro L γ δ w d LG H m up s k₀ nroot nfl hnf
  unfold kernelProt Flower.Stage1W.kernelLeavesW
  congr 1
  refine tsum_congr fun κ => ?_
  rw [kernelProt_term_none L γ δ LG up s _ hnf]

/-- Homogeneity of degree one in each leaf profile (the style of `IncTop.kernelLeavesW_scale`). -/
theorem kernelProt_scale (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (B : (Fin w × TTree.Path) → NNReal) (hB : ∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ))
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl =
      ((leafSizeProduct LG B : ℝ) : ℂ) *
        kernelProt L γ δ LG (fun a x => H a x / (B a : ℝ)) m up s fix k₀ nroot nfl := by
  unfold kernelProt leafSizeProduct
  have hprod : ∀ x : GNode LG.garden.tree → Mom d,
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (x ℓ.toNode) : ℂ) =
        ((∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ) : ℝ) : ℂ) *
          ∏ ℓ ∈ inputLeaves LG.garden, ((H ℓ.1 (x ℓ.toNode) / (B ℓ.1 : ℝ) : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hne : (B ℓ.1 : ℝ) ≠ 0 := (hB ℓ hℓ).ne'
    push_cast
    have hne' : ((B ℓ.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    field_simp
  have hsum : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
            (kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b}).indicator
              (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) =
      ((∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ) : ℝ) : ℂ) *
        (m (cosetDecoration LG.garden L k₀ κ.1) *
          ((epsDec LG.garden κ.1 : ℂ) *
            (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
              (kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b}).indicator
                (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) *
            ∏ ℓ ∈ inputLeaves LG.garden,
              ((H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) / (B ℓ.1 : ℝ) : ℝ) : ℂ))) := by
    intro κ
    rw [hprod]
    ring
  rw [tsum_congr hsum, tsum_mul_left]
  ring

/-- A vanishing leaf profile kills the protected kernel. -/
theorem kernelProt_zero_of_leaf (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    {ℓ : GLeaf LG.garden.tree} (hℓ : ℓ ∈ inputLeaves LG.garden) (h0 : H ℓ.1 = fun _ => 0)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl = 0 := by
  unfold kernelProt
  have : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
            (kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b}).indicator
              (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) = 0 := by
    intro κ
    rw [Finset.prod_eq_zero hℓ (by simp [h0]), mul_zero, mul_zero]
  simp [this]

/-- Linearity in the decoration multiplier: scalar multiples. -/
theorem kernelProt_smul_m (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (c : ℂ) (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H (fun κ => c * m κ) up s fix k₀ nroot nfl =
      c * kernelProt L γ δ LG H m up s fix k₀ nroot nfl := by
  unfold kernelProt
  simp only [mul_assoc]
  rw [tsum_mul_left]
  ring

/-- The zero multiplier gives the zero kernel. -/
theorem kernelProt_zero_m (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H (fun _ => 0) up s fix k₀ nroot nfl = 0 := by
  simp [kernelProt]

/-- Without lone parents the lone-port constraint is vacuous. -/
theorem loneConstraint_vacuous {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (hl : ∀ b, ¬ LG.garden.IsLoneParent b) :
    kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b} =
      kDomainFix LG up fix := by
  ext τ
  exact ⟨fun h => h.1, fun h => ⟨h, fun b hb => absurd hb (hl b)⟩⟩

/-- With no lone parents, `kernelProt` is main's stub kernel `FlowerP1.kernelLeavesFix` with the multiplier `m`. -/
theorem kernelProt_eq_fix_of_no_lone (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (hl : ∀ b, ¬ LG.garden.IsLoneParent b) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          m (cosetDecoration LG.garden L k₀ κ.1) *
            FlowerP1.kernelLeavesFixTerm L γ δ LG H up fix k₀ κ := by
  unfold kernelProt FlowerP1.kernelLeavesFixTerm
  simp only [loneConstraint_vacuous LG up s fix hl]

end WaveTurbulence.Flower.ProtDefs
