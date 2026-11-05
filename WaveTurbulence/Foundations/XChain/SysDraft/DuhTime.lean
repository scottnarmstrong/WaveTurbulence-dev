/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.DuhMeas

/-!
# The time integral of `node l m r` (scratch, snapshot 5)

`timeInt_node`: for `p ≤ t`,
`∫_{treeTimeDomain (node l m r) p t} ∏ e^{…} = ∫_p^t e^{iπδL^{2γ}Ω_𝔯 s} Φ_l(s) Φ̄_m(s) Φ_r(s) ds`.

The steps:
* the phase product splits at the root; the middle subtree is conjugated, its signs being reversed
  (`phaseFn_node`);
* the time domain splits (`mem_treeTimeDomain_node`): times decrease along the tree, so every subtree time
  is below the root time (`lt_root_of_isChildOf`);
* the branch times of `node l m r` are `ℝ × ℝ^{𝒩_l} × ℝ^{𝒩_m} × ℝ^{𝒩_r}` measure-preservingly
  (`timeSplit`);
* Fubini and `∫ f(x)g(y) = ∫ f ∫ g`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

section Node

variable (l m r : TTree)

/-! ### Times decrease along the tree -/

theorem lt_root_of_isChildOf {τ : GBranch (single (TTree.node l m r)) → ℝ}
    (hτ : ∀ b b' : GBranch (single (TTree.node l m r)), b'.IsChildOf b → τ b' < τ b) :
    ∀ c : GBranch (single (TTree.node l m r)), c.1.2 ≠ [] → τ c < τ (rootB l m r) := by
  intro c
  induction h : c.1.2.length using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc
    have hsplit := List.dropLast_append_getLast hc
    have hmem : c.1.2.dropLast ∈ (TTree.node l m r).branching := by
      refine TTree.branching_of_append_mem _ (i := c.1.2.getLast hc) ?_
      rw [hsplit]
      exact TTree.branching_subset_nodes _ c.2
    let c' : GBranch (single (TTree.node l m r)) := ⟨(0, c.1.2.dropLast), hmem⟩
    have hchild : c.IsChildOf c' := ⟨Subsingleton.elim _ _, c.1.2.getLast hc, hsplit.symm⟩
    have hlt := hτ c' c hchild
    by_cases hq : c.1.2.dropLast = []
    · have : c' = rootB l m r := GBranch.ext_path hq
      rw [← this]
      exact hlt
    · have hlen : c'.1.2.length < k := by
        rw [← h]
        show c.1.2.dropLast.length < c.1.2.length
        rw [List.length_dropLast]
        have := List.length_pos_of_ne_nil hc
        omega
      exact hlt.trans (ih _ hlen c' rfl hq)

/-- **The time domain of `node l m r`.** -/
theorem mem_treeTimeDomain_node {p t : ℝ} (τ : GBranch (single (TTree.node l m r)) → ℝ) :
    τ ∈ treeTimeDomain (TTree.node l m r) p t ↔
      τ (rootB l m r) ∈ Ioo p t ∧
      (fun c => τ ((isSubtreeAt_left l m r).embB c)) ∈ treeTimeDomain l p (τ (rootB l m r)) ∧
      (fun c => τ ((isSubtreeAt_mid l m r).embB c)) ∈ treeTimeDomain m p (τ (rootB l m r)) ∧
      (fun c => τ ((isSubtreeAt_right l m r).embB c)) ∈ treeTimeDomain r p (τ (rootB l m r)) := by
  constructor
  · intro h
    have hτ : ∀ b b' : GBranch (single (TTree.node l m r)), b'.IsChildOf b → τ b' < τ b :=
      fun b b' hb => (h b).2.2 b' hb
    have hr := lt_root_of_isChildOf l m r hτ
    refine ⟨⟨(h _).1, (h _).2.1⟩, fun c => ⟨(h _).1, hr _ (by simp [IsSubtreeAt.embB]),
      fun c' hc' => (h _).2.2 _ (((isSubtreeAt_left l m r).embB_isChildOf_embB_iff c' c).2 hc')⟩,
      fun c => ⟨(h _).1, hr _ (by simp [IsSubtreeAt.embB]),
      fun c' hc' => (h _).2.2 _ (((isSubtreeAt_mid l m r).embB_isChildOf_embB_iff c' c).2 hc')⟩,
      fun c => ⟨(h _).1, hr _ (by simp [IsSubtreeAt.embB]),
      fun c' hc' => (h _).2.2 _ (((isSubtreeAt_right l m r).embB_isChildOf_embB_iff c' c).2 hc')⟩⟩
  · rintro ⟨h0, hl, hm, hr⟩ c
    obtain ⟨o, rfl⟩ := (brMap_bijective l m r).2 c
    rcases o with _ | c | c | c
    · refine ⟨h0.1, h0.2, fun b' hb' => ?_⟩
      obtain ⟨o', rfl⟩ := (brMap_bijective l m r).2 b'
      obtain ⟨-, j, hj⟩ := hb'
      rcases o' with _ | c' | c' | c'
      · simp [brMap, rootB] at hj
      · exact (hl c').2.1
      · exact (hm c').2.1
      · exact (hr c').2.1
    · refine ⟨(hl c).1, (hl c).2.1.trans h0.2, fun b' hb' => ?_⟩
      obtain ⟨o', rfl⟩ := (brMap_bijective l m r).2 b'
      have hb'' := hb'
      obtain ⟨-, j, hj⟩ := hb'
      rcases o' with _ | c' | c' | c'
      · simp [brMap, rootB, IsSubtreeAt.embB] at hj
      · exact (hl c).2.2 c' (((isSubtreeAt_left l m r).embB_isChildOf_embB_iff c' c).1 hb'')
      · simp [brMap, IsSubtreeAt.embB] at hj
      · simp [brMap, IsSubtreeAt.embB] at hj
    · refine ⟨(hm c).1, (hm c).2.1.trans h0.2, fun b' hb' => ?_⟩
      obtain ⟨o', rfl⟩ := (brMap_bijective l m r).2 b'
      have hb'' := hb'
      obtain ⟨-, j, hj⟩ := hb'
      rcases o' with _ | c' | c' | c'
      · simp [brMap, rootB, IsSubtreeAt.embB] at hj
      · simp [brMap, IsSubtreeAt.embB] at hj
      · exact (hm c).2.2 c' (((isSubtreeAt_mid l m r).embB_isChildOf_embB_iff c' c).1 hb'')
      · simp [brMap, IsSubtreeAt.embB] at hj
    · refine ⟨(hr c).1, (hr c).2.1.trans h0.2, fun b' hb' => ?_⟩
      obtain ⟨o', rfl⟩ := (brMap_bijective l m r).2 b'
      have hb'' := hb'
      obtain ⟨-, j, hj⟩ := hb'
      rcases o' with _ | c' | c' | c'
      · simp [brMap, rootB, IsSubtreeAt.embB] at hj
      · simp [brMap, IsSubtreeAt.embB] at hj
      · simp [brMap, IsSubtreeAt.embB] at hj
      · exact (hr c).2.2 c' (((isSubtreeAt_right l m r).embB_isChildOf_embB_iff c' c).1 hb'')

/-! ### The phase product of `node l m r` -/

variable (L γ δ : ℝ) {d : ℕ}

/-- The root phase `e^{iπδL^{2γ}Ω_𝔯 s}`. -/
noncomputable def rootPhase (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ)) (s : ℝ) : ℂ :=
  Complex.exp ((Real.pi * δ * L ^ (2 * γ) *
    resFactor (latticePoint L (κ ((rootB l m r).child 0))) (latticePoint L (κ ((rootB l m r).child 1)))
      (latticePoint L (κ ((rootB l m r).child 2))) (latticePoint L (κ (rootB l m r).toNode)) * s : ℝ) *
    Complex.I)

theorem exp_neg_ofReal_mul_I (x : ℝ) :
    Complex.exp (((-x : ℝ) : ℂ) * Complex.I) = (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem phaseFn_node (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ))
    (τ : GBranch (single (TTree.node l m r)) → ℝ) :
    phaseFn L γ δ (TTree.node l m r) κ τ = rootPhase l m r L γ δ κ (τ (rootB l m r)) *
      (phaseFn L γ δ l ((isSubtreeAt_left l m r).res κ) (fun c => τ ((isSubtreeAt_left l m r).embB c)) *
        ((starRingEnd ℂ) (phaseFn L γ δ m ((isSubtreeAt_mid l m r).res κ)
            (fun c => τ ((isSubtreeAt_mid l m r).embB c))) *
          phaseFn L γ δ r ((isSubtreeAt_right l m r).res κ)
            (fun c => τ ((isSubtreeAt_right l m r).embB c)))) := by
  unfold phaseFn
  rw [prod_gBranch_node (M := ℂ), map_prod (starRingEnd ℂ)]
  have hroot : Complex.exp ((Real.pi * (((treeSign (TTree.node l m r) (rootB l m r).toNode : ℤˣ) : ℤ) : ℝ) *
      δ * L ^ (2 * γ) * resFactor (latticePoint L (κ ((rootB l m r).child 0)))
        (latticePoint L (κ ((rootB l m r).child 1))) (latticePoint L (κ ((rootB l m r).child 2)))
        (latticePoint L (κ (rootB l m r).toNode)) * τ (rootB l m r) : ℝ) * Complex.I) =
      rootPhase l m r L γ δ κ (τ (rootB l m r)) := by
    rw [treeSign_rootB]
    simp only [rootPhase, Units.val_one, Int.cast_one, mul_one]
  have hl : ∀ c : GBranch (single l), Complex.exp ((Real.pi *
      (((treeSign (TTree.node l m r) ((isSubtreeAt_left l m r).embB c).toNode : ℤˣ) : ℤ) : ℝ) * δ *
      L ^ (2 * γ) * resFactor (latticePoint L (κ (((isSubtreeAt_left l m r).embB c).child 0)))
        (latticePoint L (κ (((isSubtreeAt_left l m r).embB c).child 1)))
        (latticePoint L (κ (((isSubtreeAt_left l m r).embB c).child 2)))
        (latticePoint L (κ ((isSubtreeAt_left l m r).embB c).toNode)) *
        τ ((isSubtreeAt_left l m r).embB c) : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * (((treeSign l c.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        resFactor (latticePoint L ((isSubtreeAt_left l m r).res κ (c.child 0)))
          (latticePoint L ((isSubtreeAt_left l m r).res κ (c.child 1)))
          (latticePoint L ((isSubtreeAt_left l m r).res κ (c.child 2)))
          (latticePoint L ((isSubtreeAt_left l m r).res κ c.toNode)) *
        τ ((isSubtreeAt_left l m r).embB c) : ℝ) * Complex.I) := fun c => by
    rw [IsSubtreeAt.embB_toNode, treeSign_embN_left]
    rfl
  have hm : ∀ c : GBranch (single m), Complex.exp ((Real.pi *
      (((treeSign (TTree.node l m r) ((isSubtreeAt_mid l m r).embB c).toNode : ℤˣ) : ℤ) : ℝ) * δ *
      L ^ (2 * γ) * resFactor (latticePoint L (κ (((isSubtreeAt_mid l m r).embB c).child 0)))
        (latticePoint L (κ (((isSubtreeAt_mid l m r).embB c).child 1)))
        (latticePoint L (κ (((isSubtreeAt_mid l m r).embB c).child 2)))
        (latticePoint L (κ ((isSubtreeAt_mid l m r).embB c).toNode)) *
        τ ((isSubtreeAt_mid l m r).embB c) : ℝ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp ((Real.pi * (((treeSign m c.toNode : ℤˣ) : ℤ) : ℝ) * δ *
        L ^ (2 * γ) * resFactor (latticePoint L ((isSubtreeAt_mid l m r).res κ (c.child 0)))
          (latticePoint L ((isSubtreeAt_mid l m r).res κ (c.child 1)))
          (latticePoint L ((isSubtreeAt_mid l m r).res κ (c.child 2)))
          (latticePoint L ((isSubtreeAt_mid l m r).res κ c.toNode)) *
        τ ((isSubtreeAt_mid l m r).embB c) : ℝ) * Complex.I)) := fun c => by
    rw [IsSubtreeAt.embB_toNode, treeSign_embN_mid, ← exp_neg_ofReal_mul_I]
    congr 2
    push_cast
    simp only [IsSubtreeAt.res, IsSubtreeAt.embB_child]
    ring
  have hr : ∀ c : GBranch (single r), Complex.exp ((Real.pi *
      (((treeSign (TTree.node l m r) ((isSubtreeAt_right l m r).embB c).toNode : ℤˣ) : ℤ) : ℝ) * δ *
      L ^ (2 * γ) * resFactor (latticePoint L (κ (((isSubtreeAt_right l m r).embB c).child 0)))
        (latticePoint L (κ (((isSubtreeAt_right l m r).embB c).child 1)))
        (latticePoint L (κ (((isSubtreeAt_right l m r).embB c).child 2)))
        (latticePoint L (κ ((isSubtreeAt_right l m r).embB c).toNode)) *
        τ ((isSubtreeAt_right l m r).embB c) : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * (((treeSign r c.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        resFactor (latticePoint L ((isSubtreeAt_right l m r).res κ (c.child 0)))
          (latticePoint L ((isSubtreeAt_right l m r).res κ (c.child 1)))
          (latticePoint L ((isSubtreeAt_right l m r).res κ (c.child 2)))
          (latticePoint L ((isSubtreeAt_right l m r).res κ c.toNode)) *
        τ ((isSubtreeAt_right l m r).embB c) : ℝ) * Complex.I) := fun c => by
    rw [IsSubtreeAt.embB_toNode, treeSign_embN_right]
    rfl
  rw [hroot, Finset.prod_congr rfl fun c _ => hl c, Finset.prod_congr rfl fun c _ => hm c,
    Finset.prod_congr rfl fun c _ => hr c]

/-! ### The branch times of `node l m r` -/

/-- The branch bijection as an equivalence. -/
noncomputable def brEquiv :
    Unit ⊕ (GBranch (single l) ⊕ (GBranch (single m) ⊕ GBranch (single r))) ≃
      GBranch (single (TTree.node l m r)) :=
  Equiv.ofBijective _ (brMap_bijective l m r)

/-- `ℝ^{𝒩} ≃ ℝ × ℝ^{𝒩_l} × ℝ^{𝒩_m} × ℝ^{𝒩_r}` for `node l m r`. -/
noncomputable def timeSplit : (GBranch (single (TTree.node l m r)) → ℝ) ≃ᵐ
    ℝ × ((GBranch (single l) → ℝ) × ((GBranch (single m) → ℝ) × (GBranch (single r) → ℝ))) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (brEquiv l m r)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).trans
      ((MeasurableEquiv.funUnique Unit ℝ).prodCongr
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).trans
          ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))))))

theorem timeSplit_apply (τ : GBranch (single (TTree.node l m r)) → ℝ) :
    timeSplit l m r τ = (τ (rootB l m r), (fun c => τ ((isSubtreeAt_left l m r).embB c),
      (fun c => τ ((isSubtreeAt_mid l m r).embB c), fun c => τ ((isSubtreeAt_right l m r).embB c)))) :=
  rfl

theorem measurePreserving_timeSplit :
    MeasurePreserving (timeSplit l m r) volume
      ((volume : Measure ℝ).prod ((volume : Measure (GBranch (single l) → ℝ)).prod
        ((volume : Measure (GBranch (single m) → ℝ)).prod
          (volume : Measure (GBranch (single r) → ℝ))))) := by
  have h1 := (measurePreserving_piCongrLeft
    (fun _ : GBranch (single (TTree.node l m r)) => (volume : Measure ℝ)) (brEquiv l m r)).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ (GBranch (single l) ⊕ (GBranch (single m) ⊕ GBranch (single r))) =>
      (volume : Measure ℝ))
  have h3 := measurePreserving_sumPiEquivProdPi
    (fun _ : GBranch (single l) ⊕ (GBranch (single m) ⊕ GBranch (single r)) => (volume : Measure ℝ))
  have h4 := measurePreserving_sumPiEquivProdPi
    (fun _ : GBranch (single m) ⊕ GBranch (single r) => (volume : Measure ℝ))
  have h5 := measurePreserving_funUnique (volume : Measure ℝ) Unit
  exact (h5.prod (((MeasurePreserving.id _).prod h4).comp h3)).comp (h2.comp h1)

/-! ### The recursion -/

theorem measurableSet_treeTimeDomain (S : TTree) (p t : ℝ) :
    MeasurableSet (treeTimeDomain S p t) :=
  ((isOpen_domSet S p).preimage (Continuous.prodMk continuous_const continuous_id)).measurableSet

theorem treeTimeDomain_subset_box (S : TTree) (p t : ℝ) :
    treeTimeDomain S p t ⊆ Set.pi univ fun _ => Icc p t :=
  fun _ hτ c _ => ⟨(hτ c).1.le, (hτ c).2.1.le⟩

theorem integrable_timeIntegrand (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) (p t : ℝ) :
    Integrable ((treeTimeDomain S p t).indicator (phaseFn L γ δ S κ)) := by
  refine (integrable_indicator_iff (measurableSet_treeTimeDomain S p t)).2
    (Measure.integrableOn_of_bounded (M := 1) ?_ (continuous_phaseFn L γ δ S κ).aestronglyMeasurable
      (ae_of_all _ fun τ => (norm_phaseFn L γ δ S κ τ).le))
  exact (lt_of_le_of_lt (measure_mono (treeTimeDomain_subset_box S p t))
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

/-- **The time integral of `node l m r`.** -/
theorem timeInt_node (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ)) {p t : ℝ}
    (hpt : p ≤ t) :
    timeInt L γ δ (TTree.node l m r) κ p t =
      ∫ s in p..t, rootPhase l m r L γ δ κ s *
        (timeInt L γ δ l ((isSubtreeAt_left l m r).res κ) p s *
          ((starRingEnd ℂ) (timeInt L γ δ m ((isSubtreeAt_mid l m r).res κ) p s) *
            timeInt L γ δ r ((isSubtreeAt_right l m r).res κ) p s)) := by
  set κl := (isSubtreeAt_left l m r).res κ
  set κm := (isSubtreeAt_mid l m r).res κ
  set κr := (isSubtreeAt_right l m r).res κ
  set H : ℝ × ((GBranch (single l) → ℝ) × ((GBranch (single m) → ℝ) × (GBranch (single r) → ℝ))) →
      ℂ := fun z => (Ioo p t).indicator (rootPhase l m r L γ δ κ) z.1 *
    ((treeTimeDomain l p z.1).indicator (phaseFn L γ δ l κl) z.2.1 *
      ((starRingEnd ℂ) ((treeTimeDomain m p z.1).indicator (phaseFn L γ δ m κm) z.2.2.1) *
        (treeTimeDomain r p z.1).indicator (phaseFn L γ δ r κr) z.2.2.2)) with hH
  have hGH : ∀ τ, (treeTimeDomain (TTree.node l m r) p t).indicator
      (phaseFn L γ δ (TTree.node l m r) κ) τ = H (timeSplit l m r τ) := by
    intro τ
    rw [timeSplit_apply]
    simp only [hH]
    have hdom := mem_treeTimeDomain_node l m r (p := p) (t := t) τ
    by_cases hT : τ ∈ treeTimeDomain (TTree.node l m r) p t
    · obtain ⟨hA, hB, hC, hD⟩ := hdom.1 hT
      rw [Set.indicator_of_mem hT, Set.indicator_of_mem hA, Set.indicator_of_mem hB,
        Set.indicator_of_mem hC, Set.indicator_of_mem hD, phaseFn_node]
    · rw [Set.indicator_of_notMem hT]
      by_cases hA : τ (rootB l m r) ∈ Ioo p t
      · by_cases hB : (fun c => τ ((isSubtreeAt_left l m r).embB c)) ∈
            treeTimeDomain l p (τ (rootB l m r))
        · by_cases hC : (fun c => τ ((isSubtreeAt_mid l m r).embB c)) ∈
              treeTimeDomain m p (τ (rootB l m r))
          · by_cases hD : (fun c => τ ((isSubtreeAt_right l m r).embB c)) ∈
                treeTimeDomain r p (τ (rootB l m r))
            · exact absurd (hdom.2 ⟨hA, hB, hC, hD⟩) hT
            · simp [Set.indicator_of_notMem hD]
          · simp [Set.indicator_of_notMem hC]
        · simp [Set.indicator_of_notMem hB]
      · simp [Set.indicator_of_notMem hA]
  have hmp := measurePreserving_timeSplit l m r
  have hHint : Integrable H ((volume : Measure ℝ).prod ((volume : Measure (GBranch (single l) → ℝ)).prod
      ((volume : Measure (GBranch (single m) → ℝ)).prod (volume : Measure (GBranch (single r) → ℝ))))) := by
    refine (hmp.integrable_comp_emb (timeSplit l m r).measurableEmbedding).1 ?_
    have := integrable_timeIntegrand L γ δ (TTree.node l m r) κ p t
    convert this using 1
    funext τ
    exact (hGH τ).symm
  have hinner : ∀ s, ∫ y, H (s, y) ∂((volume : Measure (GBranch (single l) → ℝ)).prod
      ((volume : Measure (GBranch (single m) → ℝ)).prod (volume : Measure (GBranch (single r) → ℝ)))) =
      (Ioo p t).indicator (fun s => rootPhase l m r L γ δ κ s *
        (timeInt L γ δ l κl p s * ((starRingEnd ℂ) (timeInt L γ δ m κm p s) *
          timeInt L γ δ r κr p s))) s := by
    intro s
    simp only [hH]
    set Ql := (treeTimeDomain l p s).indicator (phaseFn L γ δ l κl)
    set Qm := (treeTimeDomain m p s).indicator (phaseFn L γ δ m κm)
    set Qr := (treeTimeDomain r p s).indicator (phaseFn L γ δ r κr)
    have e1 : ∫ a : (GBranch (single l) → ℝ) × ((GBranch (single m) → ℝ) × (GBranch (single r) → ℝ)),
        Ql a.1 * ((starRingEnd ℂ) (Qm a.2.1) * Qr a.2.2) ∂((volume : Measure (GBranch (single l) → ℝ)).prod
          ((volume : Measure (GBranch (single m) → ℝ)).prod (volume : Measure (GBranch (single r) → ℝ)))) =
        (∫ x, Ql x) * ∫ w : (GBranch (single m) → ℝ) × (GBranch (single r) → ℝ),
          (starRingEnd ℂ) (Qm w.1) * Qr w.2 ∂((volume : Measure (GBranch (single m) → ℝ)).prod
            (volume : Measure (GBranch (single r) → ℝ))) :=
      integral_prod_mul Ql
        (fun w : (GBranch (single m) → ℝ) × (GBranch (single r) → ℝ) => (starRingEnd ℂ) (Qm w.1) * Qr w.2)
    have e2 : ∫ w : (GBranch (single m) → ℝ) × (GBranch (single r) → ℝ),
        (starRingEnd ℂ) (Qm w.1) * Qr w.2 ∂((volume : Measure (GBranch (single m) → ℝ)).prod
          (volume : Measure (GBranch (single r) → ℝ))) =
        (∫ x, (starRingEnd ℂ) (Qm x)) * ∫ y, Qr y :=
      integral_prod_mul (fun x => (starRingEnd ℂ) (Qm x)) Qr
    rw [integral_const_mul, e1, e2, integral_conj, Set.indicator_mul_left]
    rfl
  calc timeInt L γ δ (TTree.node l m r) κ p t
      = ∫ τ, H (timeSplit l m r τ) := by
        unfold timeInt
        exact integral_congr_ae (ae_of_all _ hGH)
    _ = ∫ z, H z ∂((volume : Measure ℝ).prod ((volume : Measure (GBranch (single l) → ℝ)).prod
          ((volume : Measure (GBranch (single m) → ℝ)).prod
            (volume : Measure (GBranch (single r) → ℝ))))) := hmp.integral_comp' H
    _ = ∫ s, ∫ y, H (s, y) ∂((volume : Measure (GBranch (single l) → ℝ)).prod
          ((volume : Measure (GBranch (single m) → ℝ)).prod
            (volume : Measure (GBranch (single r) → ℝ)))) := integral_prod H hHint
    _ = ∫ s, (Ioo p t).indicator (fun s => rootPhase l m r L γ δ κ s *
          (timeInt L γ δ l κl p s * ((starRingEnd ℂ) (timeInt L γ δ m κm p s) *
            timeInt L γ δ r κr p s))) s := integral_congr_ae (ae_of_all _ hinner)
    _ = _ := by
        rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
          intervalIntegral.integral_of_le hpt]

end Node

end WaveTurbulence.SysAPI
