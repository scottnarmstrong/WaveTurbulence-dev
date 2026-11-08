/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Time

/-! # D2c PROT-CUT: integrating out one free branch (the pin identity)

`protTime_pin`: for a free branch `a`,
`protTime fix = ∫ u, 1[u ∈ pinSet] · protTime (fix with a pinned at u)`.
The constraints on `u` dropped by `kDomainFix` when `a` becomes designated are listed in `pinSet`: the layer and
upper-clock constraints of `a`, the order constraints between `a` and its designated parent or children, and the
lone-port constraint if `a` is a lone parent. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtCut

open WaveTurbulence.Flower.ProtDefs

variable {w d : ℕ} {T : Fin w → TTree}

/-- The constraints of a free branch `a` that `kDomainFix` drops when `a` is designated at `u`. -/
def pinSet (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (a : GBranch LG.garden.tree) : Set ℝ :=
  {u | (LG.layer a.toNode : ℝ) < u ∧ u < LG.layer a.toNode + 1 ∧ 0 < u ∧ u < up a ∧
    (∀ b' : GBranch LG.garden.tree, b'.IsChildOf a → ∀ σ, fix b' = some σ → σ < u) ∧
    (∀ b : GBranch LG.garden.tree, a.IsChildOf b → ∀ σ, fix b = some σ → u < σ) ∧
    (LG.garden.IsLoneParent a → s < u)}

theorem measurableSet_pinSet (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (a : GBranch LG.garden.tree) :
    MeasurableSet (pinSet LG up s fix a) := by
  unfold pinSet
  simp only [Set.ofPred_and]
  refine (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter
        ((measurableSet_lt measurable_id measurable_const).inter ?_)))
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (measurableSet_imp _
    (measurableSet_lt measurable_const measurable_id)))
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun b' => measurableSet_imp _ ?_
    cases h : fix b' with
    | none => simp only [reduceCtorEq, false_implies, implies_true]; exact MeasurableSet.univ
    | some v => simp only [Option.some.injEq, forall_eq']; exact measurableSet_Ioi
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun b => measurableSet_imp _ ?_
    cases h : fix b with
    | none => simp only [reduceCtorEq, false_implies, implies_true]; exact MeasurableSet.univ
    | some v => simp only [Option.some.injEq, forall_eq']; exact measurableSet_Iio

theorem pinSet_subset (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (a : GBranch LG.garden.tree) :
    pinSet LG up s fix a ⊆ Ioo (LG.layer a.toNode : ℝ) (LG.layer a.toNode + 1) :=
  fun _ hu => ⟨hu.1, hu.2.1⟩

theorem isChildOf_ne {T : Fin w → TTree} {b' b : GBranch T} (h : b'.IsChildOf b) : b' ≠ b := by
  rintro rfl
  obtain ⟨-, i, hi⟩ := h
  have := congrArg List.length hi
  simp at this

/-- **The domain with one more designated branch.** -/
theorem mem_protDom_update (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (a : GBranch LG.garden.tree) (ha : fix a = none)
    (u : ℝ) (τ : GBranch LG.garden.tree → ℝ) (hτa : τ a = u)
    (hτ : ∀ b σ, fix b = some σ → τ b = σ) :
    τ ∈ protDom LG up s fix ↔
      u ∈ pinSet LG up s fix a ∧ τ ∈ protDom LG up s (Function.update fix a (some u)) := by
  classical
  have hupd : ∀ b, b ≠ a → Function.update fix a (some u) b = fix b := fun b hb =>
    Function.update_of_ne hb _ _
  have hupa : Function.update fix a (some u) a = some u := Function.update_self _ _ _
  constructor
  · rintro ⟨hD, hL⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun b => ⟨fun hb => ?_, fun b' hb' hor => ?_⟩, fun b hb hf => ?_⟩⟩
    · have := ((hD a).1 ha).1; rwa [hτa] at this
    · have := ((hD a).1 ha).2.1; rwa [hτa] at this
    · have := ((hD a).1 ha).2.2.1; rwa [hτa] at this
    · have := ((hD a).1 ha).2.2.2; rwa [hτa] at this
    · intro b' hb' σ hσ
      have := (hD a).2 b' hb' (Or.inr ha)
      rwa [hτ b' σ hσ, hτa] at this
    · intro b hb σ hσ
      have := (hD b).2 a hb (Or.inl ha)
      rwa [hτ b σ hσ, hτa] at this
    · intro hl
      have := hL a hl ha
      rwa [hτa] at this
    · have hba : b ≠ a := by rintro rfl; rw [hupa] at hb; simp at hb
      rw [hupd b hba] at hb
      exact (hD b).1 hb
    · refine (hD b).2 b' hb' ?_
      rcases hor with h | h
      · have hba : b' ≠ a := by rintro rfl; rw [hupa] at h; simp at h
        exact Or.inl (by rwa [hupd b' hba] at h)
      · have hba : b ≠ a := by rintro rfl; rw [hupa] at h; simp at h
        exact Or.inr (by rwa [hupd b hba] at h)
    · have hba : b ≠ a := by rintro rfl; rw [hupa] at hf; simp at hf
      exact hL b hb (by rwa [hupd b hba] at hf)
  · rintro ⟨⟨h1, h2, h3, h4, hc, hp, hl⟩, hD, hL⟩
    refine ⟨fun b => ⟨fun hb => ?_, fun b' hb' hor => ?_⟩, fun b hb hf => ?_⟩
    · by_cases hba : b = a
      · subst hba; rw [hτa]; exact ⟨h1, h2, h3, h4⟩
      · exact (hD b).1 (by rw [hupd b hba]; exact hb)
    · by_cases hba : b = a
      · subst hba
        have hne : b' ≠ b := isChildOf_ne hb'
        cases hf : fix b' with
        | none => exact (hD b).2 b' hb' (Or.inl (by rw [hupd b' hne]; exact hf))
        | some σ => rw [hτ b' σ hf, hτa]; exact hc b' hb' σ hf
      · by_cases hb'a : b' = a
        · subst hb'a
          cases hf : fix b with
          | none => exact (hD b).2 b' hb' (Or.inr (by rw [hupd b hba]; exact hf))
          | some σ => rw [hτ b σ hf, hτa]; exact hp b hb' σ hf
        · refine (hD b).2 b' hb' ?_
          rw [hupd b hba, hupd b' hb'a]
          exact hor
    · by_cases hba : b = a
      · subst hba; rw [hτa]; exact hl hb
      · exact hL b hb (by rw [hupd b hba]; exact hf)

/-- The free branches after designating `a`, as a subtype of the free branches before. -/
def pinEquiv (fix : GBranch T → Option ℝ) (a : GBranch T) (ha : fix a = none) (u : ℝ) :
    {x : {b : GBranch T // fix b = none} // ¬ x = ⟨a, ha⟩} ≃
      {b : GBranch T // Function.update fix a (some u) b = none} where
  toFun x := ⟨x.1.1, by
    classical
    have hne : x.1.1 ≠ a := fun h => x.2 (Subtype.ext h)
    rw [Function.update_of_ne hne]; exact x.1.2⟩
  invFun b := ⟨⟨b.1, by
    classical
    by_cases hba : b.1 = a
    · exact absurd b.2 (by rw [hba, Function.update_self]; simp)
    · have := b.2; rwa [Function.update_of_ne hba] at this⟩, by
    classical
    intro h
    have hba : b.1 = a := congrArg Subtype.val h
    exact absurd b.2 (by rw [hba, Function.update_self]; simp)⟩
  left_inv x := rfl
  right_inv b := rfl

/-- **The pin identity**: a free branch `a` is integrated out as an outer time `u`. -/
theorem protTime_pin (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d)
    (a : GBranch LG.garden.tree) (ha : fix a = none) :
    protTime L γ δ LG up s fix K =
      ∫ u, (pinSet LG up s fix a).indicator
        (fun u => protTime L γ δ LG up s (Function.update fix a (some u)) K) u := by
  classical
  set F := {b : GBranch LG.garden.tree // fix b = none}
  set a' : F := ⟨a, ha⟩
  let p : F → Prop := fun x => x = a'
  let e₁ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : F => ℝ) p
  have he₁ : MeasurePreserving e₁ volume (volume.prod volume) := by
    have h := measurePreserving_piEquivPiSubtypeProd (fun _ : F => (volume : Measure ℝ)) p
    simp only [← volume_pi] at h
    convert h using 3
    congr 1
    exact Subsingleton.elim _ _
  let e₂ := (MeasurableEquiv.funUnique {x // p x} ℝ).prodCongr
    (MeasurableEquiv.refl ({x // ¬ p x} → ℝ))
  have he₂ : MeasurePreserving e₂ (volume.prod volume) (volume.prod volume) := by
    have h1 : MeasurePreserving (MeasurableEquiv.funUnique {x // p x} ℝ) volume volume := by
      have h := measurePreserving_funUnique (volume : Measure ℝ) {x // p x}
      simp only [← volume_pi] at h
      convert h using 2
      congr 1
      try exact Subsingleton.elim _ _
    exact h1.prod (MeasurePreserving.id _)
  let Φ := e₁.trans e₂
  have hΦ : MeasurePreserving Φ volume (volume.prod volume) := he₂.comp he₁
  set f := protIntegrand L γ δ LG up s fix K with hf
  let g : ℝ × ({x // ¬ p x} → ℝ) → ℂ := fun z => f (Φ.symm z)
  have hfg : ∀ τ, f τ = g (Φ τ) := fun τ => by simp [g]
  have hint : Integrable g (volume.prod volume) := by
    have := (hΦ.integrable_comp_emb Φ.measurableEmbedding (g := g)).mp
    refine this ?_
    have hc : g ∘ Φ = f := funext fun τ => (hfg τ).symm
    rw [hc]
    exact integrable_protIntegrand L γ δ LG up s fix K
  have step1 : protTime L γ δ LG up s fix K = ∫ z, g z ∂(volume.prod volume) := by
    unfold protTime
    change ∫ τ, f τ = _
    simp_rw [hfg]
    exact hΦ.integral_comp' g
  rw [step1, integral_prod g hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  -- the inner integral at fixed `u`
  have hsymm : ∀ σ : {x // ¬ p x} → ℝ, ∀ x : F, (Φ.symm (u, σ)) x = if h : x = a' then u else σ ⟨x, h⟩ := by
    intro σ x
    rfl
  set fix' := Function.update fix a (some u)
  have hfa : fix' a = some u := Function.update_self _ _ _
  have hfb : ∀ b, b ≠ a → fix' b = fix b := fun b hb => Function.update_of_ne hb _ _
  let eu := pinEquiv fix a ha u
  have hext : ∀ σ : {x // ¬ p x} → ℝ,
      LG.garden.extendFix fix (Φ.symm (u, σ)) = LG.garden.extendFix fix' (fun b => σ (eu.symm b)) := by
    intro σ
    funext b
    by_cases hba : b = a
    · subst hba
      rw [extendFix_free LG.garden fix _ a', hsymm, dite_eq_left_of_eq_true (eq_true rfl),
        extendFix_some LG.garden fix' _ hfa]
    · cases hb : fix b with
      | some v =>
        rw [extendFix_some LG.garden fix _ hb,
          extendFix_some LG.garden fix' _ (by rw [hfb b hba]; exact hb)]
      | none =>
        have hb' : fix' b = none := by rw [hfb b hba]; exact hb
        rw [extendFix_free LG.garden fix _ ⟨b, hb⟩, extendFix_free LG.garden fix' _ ⟨b, hb'⟩, hsymm,
          dite_eq_right_of_eq_false (eq_false (fun h => hba (congrArg Subtype.val h)))]
        rfl
  have hpt : ∀ σ : {x // ¬ p x} → ℝ, g (u, σ) =
      (pinSet LG up s fix a).indicator 1 u *
        protIntegrand L γ δ LG up s fix' K (fun b => σ (eu.symm b)) := by
    intro σ
    simp only [g, hf, protIntegrand]
    rw [hext σ]
    set τ := LG.garden.extendFix fix' (fun b => σ (eu.symm b))
    have hτa : τ a = u := extendFix_some LG.garden fix' _ hfa
    have hτ : ∀ b v, fix b = some v → τ b = v := by
      intro b v hv
      have hba : b ≠ a := by rintro rfl; rw [ha] at hv; simp at hv
      exact extendFix_some LG.garden fix' _ (by rw [hfb b hba]; exact hv)
    have key := mem_protDom_update LG up s fix a ha u τ hτa hτ
    by_cases hu : u ∈ pinSet LG up s fix a
    · rw [Set.indicator_of_mem hu, Pi.one_apply, one_mul]
      by_cases hD : τ ∈ protDom LG up s fix'
      · rw [Set.indicator_of_mem (key.2 ⟨hu, hD⟩), Set.indicator_of_mem hD]
      · rw [Set.indicator_of_notMem (fun h => hD (key.1 h).2), Set.indicator_of_notMem hD]
    · rw [Set.indicator_of_notMem hu, zero_mul, Set.indicator_of_notMem (fun h => hu (key.1 h).1)]
  simp_rw [hpt]
  rw [integral_const_mul]
  rw [integral_arrow_equiv eu (protIntegrand L γ δ LG up s fix' K)]
  by_cases hu : u ∈ pinSet LG up s fix a
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Pi.one_apply, one_mul]
    rfl
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]

end WaveTurbulence.Flower.ProtCut
