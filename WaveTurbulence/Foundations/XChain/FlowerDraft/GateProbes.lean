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

theorem fixPat_plain {w : ℕ} (LG : LayeredGarden w) (t s : ℝ) (b : GBranch LG.garden.tree) :
    LG.fixPat (fun _ => FixPat.plain) t s b = if LG.garden.IsFlowerParent b then some s else none := by
  classical
  unfold LayeredGarden.fixPat
  split_ifs <;> rfl

theorem dyadicCut_zero (L x : ℝ) : dyadicCut L 0 x = chi0 (x / L) := by
  simp [dyadicCut]

/-- Two flower parents in the same tree of a flower garden coincide. -/
theorem flowerParent_unique {w : ℕ} {G : Garden w} (hG : G.IsFlowerGarden) {b b' : GBranch G.tree}
    (hb : G.IsFlowerParent b) (hb' : G.IsFlowerParent b') (hj : b.1.1 = b'.1.1) : b = b' := by
  classical
  obtain ⟨ℓ, hℓ, hbℓ⟩ := hb
  obtain ⟨ℓ', hℓ', hbℓ'⟩ := hb'
  have hmark : ∀ ℓ₀ : GLeaf G.tree, G.IsFlower ℓ₀ → G.mark ℓ₀ ≠ none := fun ℓ₀ h => by
    rw [show G.mark ℓ₀ = _ from h]
    simp
  have hℓℓ' : ℓ = ℓ' := by
    have hc := hG.1 ℓ.1.1
    have h1 : ℓ ∈ Finset.univ.filter fun x : GLeaf G.tree => x.1.1 = ℓ.1.1 ∧ G.mark x ≠ none :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hmark ℓ hℓ⟩
    have h2 : ℓ' ∈ Finset.univ.filter fun x : GLeaf G.tree => x.1.1 = ℓ.1.1 ∧ G.mark x ≠ none :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hbℓ'.1, ← hj, ← hbℓ.1], hmark ℓ' hℓ'⟩
    exact Finset.card_le_one.1 hc.le ℓ h1 ℓ' h2
  subst hℓℓ'
  obtain ⟨-, i, hi⟩ := hbℓ
  obtain ⟨-, i', hi'⟩ := hbℓ'
  have hpath : b.1.2 = b'.1.2 := by
    have := hi.symm.trans hi'
    have h := congrArg List.dropLast this
    simpa using h
  exact Subtype.ext (Prod.ext hj hpath)

/-- A flower garden has no lone leaves. -/
theorem not_isLoneParent {w : ℕ} {G : Garden w} (hG : G.IsFlowerGarden) (b : GBranch G.tree) :
    ¬ G.IsLoneParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  have h := hG.2.1 ℓ (by rw [show G.mark ℓ = _ from hℓ]; simp)
  rw [Garden.IsFlower, show G.mark ℓ = _ from hℓ] at h
  exact absurd h (by simp)

variable (L γ δ : ℝ) {d : ℕ}

/-- **Bridge:** with only the flower parents designated (time `s`), no removed phases and weight `1`,
`kernelKgen` is `kernelK`. Hypotheses: a flower garden, flower parents in layer `p`, and
`p < s < p + 1`, `0 < s < t`. -/
theorem kernelKgen_flowerParents {w : ℕ} (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (p : ℕ)
    (hG : LG.garden.IsFlowerGarden)
    (hlay : ∀ b, LG.garden.IsFlowerParent b → LG.layer b.toNode = p) {t s : ℝ}
    (hs : (p : ℝ) < s ∧ s < p + 1) (hs0 : 0 < s) (hst : s < t) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelKgen L γ δ F LG (fun b => if LG.garden.IsFlowerParent b then some s else none) ∅
        (fun _ => 1) (fun _ => t) k₀ nroot nfl =
      kernelK L γ δ F LG (fun _ => t) s k₀ nroot nfl := by
  classical
  unfold kernelKgen kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  simp only [Complex.ofReal_one, mul_one]
  congr 2
  set fix : GBranch LG.garden.tree → Option ℝ :=
    fun b => if LG.garden.IsFlowerParent b then some s else none with hfix
  have hfree : ∀ b, fix b = none ↔ ¬ LG.garden.IsFlowerParent b := fun b => by
    simp only [hfix]
    split_ifs with h <;> simp [h]
  have hoff : phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k₀ κ.1) =
      phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) := by
    funext τ
    simp [phaseProdOff, phaseProd]
  rw [hoff]
  unfold phaseIntegral
  have hext : ∀ τ : LG.garden.FreeBranch → ℝ, LG.garden.extendTime s τ =
      LG.garden.extendFix fix (fun q => τ ⟨q.1, (hfree q.1).1 q.2⟩) := by
    intro τ
    funext b
    unfold Garden.extendTime Garden.extendFix
    by_cases hb : LG.garden.IsFlowerParent b
    · simp only [hb, ↓reduceDIte]
      split
      · rename_i v hv
        simp only [hfix, hb, ↓reduceIte, Option.some.injEq] at hv
        exact hv
      · rename_i hv
        simp [hfix, hb] at hv
    · simp only [hb, ↓reduceDIte]
      split
      · rename_i v hv
        simp [hfix, hb] at hv
      · rfl
  have hdom : ∀ σ : GBranch LG.garden.tree → ℝ, (∀ b, LG.garden.IsFlowerParent b → σ b = s) →
      (σ ∈ kDomainFix LG (fun _ => t) fix ↔ σ ∈ kDomain LG (fun _ => t) s) := by
    intro σ hσ
    constructor
    · intro h b
      by_cases hb : LG.garden.IsFlowerParent b
      · have hlb := hlay b hb
        rw [hσ b hb, hlb]
        refine ⟨hs.1, hs.2, hs0, hst, fun b' hb' => ?_, fun h' => absurd h' (not_isLoneParent hG b)⟩
        have hb'free : ¬ LG.garden.IsFlowerParent b' := fun hb'' => by
          have := flowerParent_unique hG hb hb'' hb'.1.symm
          subst this
          obtain ⟨-, i, hi⟩ := hb'
          have := congrArg List.length hi
          simp at this
        have := (h b).2 b' hb' (Or.inl ((hfree b').2 hb'free))
        rwa [hσ b hb] at this
      · obtain ⟨h1, h2, h3, h4⟩ := (h b).1 ((hfree b).2 hb)
        exact ⟨h1, h2, h3, h4, fun b' hb' => (h b).2 b' hb' (Or.inr ((hfree b).2 hb)),
          fun h' => absurd h' (not_isLoneParent hG b)⟩
    · intro h b
      refine ⟨fun _ => ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.1⟩, fun b' hb' _ =>
        (h b).2.2.2.2.1 b' hb'⟩
  have key := integral_subtype_congr (Pp := fun b => ¬ LG.garden.IsFlowerParent b)
    (Q := fun b => fix b = none) (fun b => (hfree b).symm)
    (fun σ => (kDomainFix LG (fun _ => t) fix).indicator
      (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix σ))
  refine key.symm.trans ?_
  show ∫ τ : LG.garden.FreeBranch → ℝ, _ = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [← hext τ]
  have hσ : ∀ b, LG.garden.IsFlowerParent b → LG.garden.extendTime s τ b = s := fun b hb => by
    simp [Garden.extendTime, hb]
  by_cases hmem : LG.garden.extendTime s τ ∈ kDomain LG (fun _ => t) s
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hdom _ hσ).2 hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem ((hdom _ hσ).1 h))]

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

/-- The support of the `finsum` defining `flowerSumP` is finite. -/
theorem finite_flowerSum_support (P : WTParams) (p N w : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
    (ζ : ℤˣ) :
    {LG : LayeredGarden w | IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid p j (pat j)}.Finite := by
  refine (WaveBProbes.finite_layeredGardens w N p).subset ?_
  rintro LG ⟨h, -, hN, -⟩
  exact ⟨hN.le, h.2.2.1⟩

/-- The support of the `finsum` defining `coupleSum` is finite. -/
theorem finite_coupleSum_support (P : WTParams) (p N : ℕ) (kind : TreeKind) (dt : Bool) :
    {LG : LayeredGarden 2 | IsCanonC (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.TreeKindOK p (P.N (p + 1)) kind ∧
      (dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree,
        b.1 = (j, []) ∧ LG.layer b.toNode = p)}.Finite := by
  refine (WaveBProbes.finite_layeredGardens 2 N p).subset ?_
  rintro LG ⟨h, -, hN, -⟩
  exact ⟨hN.le, h.2.1⟩

end WaveTurbulence.FlowerProbes
