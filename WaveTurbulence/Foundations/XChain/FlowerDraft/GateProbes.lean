/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.XChain.WaveBDraft.CoreProbes

/-!
# Probes for the B1.12 redraft (not frozen)

* `kernelKgen_flowerParents`: for flower gardens with the flower parents in layer `p`,
  `p < s < min(t, p+1)`, and only the flower parents designated, the general kernel is `kernelK`. So
  `kernelKgen` is a conservative generalization, and plain `flowerSumP` is the old `truncSumHζ` with the
  F39/F46 kinds.
* `coupleSum_tr`: the kind-`a^tr` couple sum without `∂_t` is `truncSumC`.
* `finite_flowerSum_support`, `finite_coupleSum_support`: the `finsum`s defining `flowerSumP` and `coupleSum`
  have finite support. They replace snapshot 5's `finite_truncSumHζ_support`.
* `fixPat_plain`, `dyadicCut_zero`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.FlowerProbes

theorem ite_of_true {c : Prop} [Decidable c] {α : Sort*} (a b : α) (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_of_false {c : Prop} [Decidable c] {α : Sort*} (a b : α) (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- Integrals over function spaces on two subtypes defined by equivalent predicates agree. -/
theorem integral_subtype_congr {ι : Type*} [Fintype ι] {Pp Q : ι → Prop} [DecidablePred Pp]
    [DecidablePred Q] (h : ∀ i, Pp i ↔ Q i) (G : ({i // Q i} → ℝ) → ℂ) :
    ∫ τ : {i // Pp i} → ℝ, G (fun q => τ ⟨q.1, (h q.1).2 q.2⟩) = ∫ σ : {i // Q i} → ℝ, G σ := by
  let e : {i // Pp i} ≃ {i // Q i} := Equiv.subtypeEquivRight h
  have hmp := measurePreserving_piCongrLeft (fun _ : {i // Q i} => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : {i // Q i} => ℝ) e) G
  convert this using 2 with τ
  funext τ
  congr 1

variable (L γ δ : ℝ) {d : ℕ}

/-- **Bridge (no designated nodes):** for a plain garden, `kernelKgen` with no designated nodes, no removed
phases and weight `1` is `kernelK` (for any `s`: a plain garden has no flower or lone parents). -/
theorem kernelKgen_noFix {w : ℕ} (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up k₀ nroot nfl =
      kernelK L γ δ F LG up s k₀ nroot nfl := by
  classical
  have hnf : ∀ b, ¬ LG.garden.IsFlowerParent b := fun b ⟨ℓ, hℓ, _⟩ => by
    rw [Garden.IsFlower, hP ℓ] at hℓ
    exact absurd hℓ (by simp)
  have hnl : ∀ b, ¬ LG.garden.IsLoneParent b := fun b ⟨ℓ, hℓ, _⟩ => by
    rw [Garden.IsLone, hP ℓ] at hℓ
    exact absurd hℓ (by simp)
  unfold kernelKgen kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  simp only [Complex.ofReal_one, mul_one]
  congr 2
  have hoff : phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k₀ κ.1) =
      phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) := by
    funext τ
    simp [phaseProdOff, phaseProd]
  rw [hoff]
  unfold phaseIntegral
  have hfree : ∀ b : GBranch LG.garden.tree, (none : Option ℝ) = none ↔ ¬ LG.garden.IsFlowerParent b :=
    fun b => ⟨fun _ => hnf b, fun _ => rfl⟩
  have key := integral_subtype_congr (Pp := fun b => ¬ LG.garden.IsFlowerParent b)
    (Q := fun _ => (none : Option ℝ) = none) (fun b => (hfree b).symm)
    (fun σ => (kDomainFix LG up (fun _ => none)).indicator
      (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1))
        (LG.garden.extendFix (fun _ => none) σ))
  refine key.symm.trans ?_
  show ∫ τ : LG.garden.FreeBranch → ℝ, _ = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  have hext : LG.garden.extendFix (fun _ => none) (fun q => τ ⟨q.1, hnf q.1⟩) =
      LG.garden.extendTime s τ := by
    funext b
    simp [Garden.extendFix, Garden.extendTime, hnf b]
  rw [hext]
  have hdom : LG.garden.extendTime s τ ∈ kDomainFix LG up (fun _ => none) ↔
      LG.garden.extendTime s τ ∈ kDomain LG up s := by
    constructor
    · intro h b
      obtain ⟨h1, h2, h3, h4⟩ := (h b).1 rfl
      exact ⟨h1, h2, h3, h4, fun b' hb' => (h b).2 b' hb' (Or.inl rfl), fun h' => absurd h' (hnl b)⟩
    · intro h b
      exact ⟨fun _ => ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.1⟩, fun b' hb' _ =>
        (h b).2.2.2.2.1 b' hb'⟩
  by_cases hmem : LG.garden.extendTime s τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hdom.2 hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h => hmem (hdom.1 h))]

/-- **Bridge:** the kind-`a^tr` couple sum without `∂_t` is `truncSumC` (so B1.12 (2) extends B1.2's couple
objects). -/
theorem coupleSum_tr (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) (k : Mom P.d) :
    coupleSum P F p N .tr false t k = truncSumC P F (p + 1) N t k := by
  classical
  unfold coupleSum truncSumC
  refine finsum_congr fun LG => ?_
  rw [finsum_eq_if, finsum_eq_if]
  have hiff : (IsCanonC (p + 1) LG ∧ (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧
      LG.garden.order = N ∧ LG.TreeKindOK p (P.N (p + 1)) .tr ∧
      (false = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)) ↔
      (IsCanonC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
        LG.garden.order = N) := by
    simp only [Nat.add_sub_cancel, LayeredGarden.IsTrunc, LayeredGarden.TreeKindOK]
    tauto
  by_cases h : IsCanonC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LG.garden.order = N
  · rw [ite_of_true _ _ (hiff.2 h), ite_of_true _ _ h]
    have hfix : (fun b : GBranch LG.garden.tree =>
        if false = true ∧ b.1.2 = [] then some t else none) = fun _ => none := by
      funext b
      simp
    rw [hfix, kernelKgen_noFix P.L P.γ P.δ F LG h.1.1.1 _ 0]
    unfold KQ KQstar
    simp only [ite_self]
  · rw [ite_of_false _ _ (fun h' => h (hiff.1 h')), ite_of_false _ _ h]

/-! ### Finite supports -/

end WaveTurbulence.FlowerProbes
