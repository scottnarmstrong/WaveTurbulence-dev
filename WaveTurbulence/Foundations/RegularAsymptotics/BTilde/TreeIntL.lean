/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeInt

/-!
# Fubini along a tree with a lone leaf

DH21 (varat) (L1698–L1703) integrates `∏_𝔫 e^{ζ_𝔫πiα_𝔫t_𝔫}` over the time domain of a regular tree
with the extra condition `t_{(ℓ_*)^p} > s` at the parent of the lone leaf `ℓ_*`. Here the lone leaf is
at the path `lp` (`none`: no lone leaf). The recursive domain `treeDomL` and the iterated integral
`treeIntL` carry the condition `lp = some [] → s < u` (a lone leaf at the root of a subtree whose parent
has time `u`); at a leaf this is the condition at the lone leaf's parent, at a node it is vacuous for a
lone leaf at a leaf. `integral_treeDomL` is Fubini; `lp = none` gives `integral_treeDomR` (no lone
leaf: DH21 (defcoefa2)).
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree MeasureTheory Complex Set
open scoped Real

/-- The lone-leaf path seen from the `i`-th subtree. -/
def subLone : Option TTree.Path → Fin 3 → Option TTree.Path
  | some (j :: q), i => if j = i then some q else none
  | _, _ => none

theorem subLone_none (i : Fin 3) : subLone none i = none := rfl

/-- The condition of a lone leaf at the root of a subtree with parent time `u`. -/
def LoneOK (lp : Option TTree.Path) (s u : ℝ) : Prop := lp = some [] → s < u

noncomputable instance (lp : Option TTree.Path) (s u : ℝ) : Decidable (LoneOK lp s u) := by
  unfold LoneOK; infer_instance

theorem loneOK_none (s u : ℝ) : LoneOK none s u := fun h => by cases h

/-- **The recursive time domain with a lone leaf at `lp`.** -/
def treeDomL : (T : TTree) → Option TTree.Path → ℝ → ℝ → Set (TB T → ℝ)
  | .leaf, lp, s, u => {_τ | LoneOK lp s u}
  | .node l m r, lp, s, u => {τ | LoneOK lp s u ∧ 0 < tRoot τ ∧ tRoot τ < u ∧
      tL τ ∈ treeDomL l (subLone lp 0) s (tRoot τ) ∧ tM τ ∈ treeDomL m (subLone lp 1) s (tRoot τ) ∧
      tR τ ∈ treeDomL r (subLone lp 2) s (tRoot τ)}

/-- **The iterated time integral with a lone leaf at `lp`.** -/
noncomputable def treeIntL : TTree → Option TTree.Path → (TTree.Path → ℝ) → ℝ → ℝ → ℂ
  | .leaf, lp, _, s, u => if LoneOK lp s u then 1 else 0
  | .node l m r, lp, β, s, u => (if LoneOK lp s u then 1 else 0) * ∫ τ in (0 : ℝ)..u,
      cexp (π * I * (β [] * τ)) * (treeIntL l (subLone lp 0) (fun p => β (0 :: p)) s τ *
        treeIntL m (subLone lp 1) (fun p => β (1 :: p)) s τ *
          treeIntL r (subLone lp 2) (fun p => β (2 :: p)) s τ)

theorem treeDomL_none : ∀ (T : TTree) (s u : ℝ), treeDomL T none s u = treeDomR T u
  | .leaf, s, u => by
    ext τ; simp [treeDomL, treeDomR, loneOK_none]
  | .node l m r, s, u => by
    ext τ
    simp only [treeDomL, treeDomR, subLone_none, Set.mem_ofPred_eq, treeDomL_none l, treeDomL_none m,
      treeDomL_none r, loneOK_none, true_and]

theorem treeIntL_none : ∀ (T : TTree) (β : TTree.Path → ℝ) (s u : ℝ),
    treeIntL T none β s u = treeInt T β u
  | .leaf, β, s, u => by simp [treeIntL, treeInt, loneOK_none]
  | .node l m r, β, s, u => by
    simp only [treeIntL, treeInt, subLone_none, treeIntL_none l, treeIntL_none m, treeIntL_none r,
      loneOK_none, ite_true, one_mul]

section Fubini

theorem isOpen_treeDomL : ∀ (T : TTree) (lp : Option TTree.Path) (s : ℝ),
    IsOpen {p : ℝ × (TB T → ℝ) | p.2 ∈ treeDomL T lp s p.1}
  | .leaf, lp, s => by
    by_cases h : lp = some []
    · have e : {p : ℝ × (TB TTree.leaf → ℝ) | p.2 ∈ treeDomL TTree.leaf lp s p.1} = {p | s < p.1} := by
        ext p; simp [treeDomL, LoneOK, h]
      rw [e]
      exact isOpen_lt continuous_const continuous_fst
    · have e : {p : ℝ × (TB TTree.leaf → ℝ) | p.2 ∈ treeDomL TTree.leaf lp s p.1} = Set.univ := by
        ext p; simp [treeDomL, LoneOK, h]
      rw [e]
      exact isOpen_univ
  | .node l m r, lp, s => by
    have hl := isOpen_treeDomL l (subLone lp 0) s
    have hm := isOpen_treeDomL m (subLone lp 1) s
    have hr := isOpen_treeDomL r (subLone lp 2) s
    have hR : Continuous fun p : ℝ × (TB (.node l m r) → ℝ) => tRoot p.2 :=
      (continuous_tRoot l m r).comp continuous_snd
    have hL : IsOpen {p : ℝ × (TB (.node l m r) → ℝ) | LoneOK lp s p.1} := by
      by_cases h : lp = some []
      · simp only [LoneOK, h, forall_const]
        exact isOpen_lt continuous_const continuous_fst
      · simp only [LoneOK, h, IsEmpty.forall_iff, Set.ofPred_true]
        exact isOpen_univ
    have e : {p : ℝ × (TB (.node l m r) → ℝ) | p.2 ∈ treeDomL (.node l m r) lp s p.1} =
        {p | LoneOK lp s p.1} ∩ {p | 0 < tRoot p.2} ∩ {p | tRoot p.2 < p.1} ∩
          ((fun p : ℝ × (TB (.node l m r) → ℝ) => (tRoot p.2, tL p.2)) ⁻¹'
            {p : ℝ × (TB l → ℝ) | p.2 ∈ treeDomL l (subLone lp 0) s p.1}) ∩
          ((fun p : ℝ × (TB (.node l m r) → ℝ) => (tRoot p.2, tM p.2)) ⁻¹'
            {p : ℝ × (TB m → ℝ) | p.2 ∈ treeDomL m (subLone lp 1) s p.1}) ∩
          ((fun p : ℝ × (TB (.node l m r) → ℝ) => (tRoot p.2, tR p.2)) ⁻¹'
            {p : ℝ × (TB r → ℝ) | p.2 ∈ treeDomL r (subLone lp 2) s p.1}) := by
      ext p
      simp only [treeDomL, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [e]
    refine (((((hL.inter (isOpen_lt continuous_const hR)).inter (isOpen_lt hR continuous_fst)).inter
      (hl.preimage (hR.prodMk ((continuous_tL l m r).comp continuous_snd)))).inter
      (hm.preimage (hR.prodMk ((continuous_tM l m r).comp continuous_snd)))).inter
      (hr.preimage (hR.prodMk ((continuous_tR l m r).comp continuous_snd))))

theorem measurableSet_treeDomL (T : TTree) (lp : Option TTree.Path) (s u : ℝ) :
    MeasurableSet (treeDomL T lp s u) := by
  have h := (isOpen_treeDomL T lp s).preimage (continuous_const.prodMk continuous_id :
    Continuous fun τ : TB T → ℝ => (u, τ))
  exact h.measurableSet

theorem treeDomL_subset : ∀ (T : TTree) (lp : Option TTree.Path) (s u : ℝ),
    treeDomL T lp s u ⊆ {τ | ∀ p, τ p ∈ Icc 0 u}
  | .leaf, _, _, _ => fun τ _ p => absurd p.2 (not_mem_branching_leaf _)
  | .node l m r, lp, s, u => by
    rintro τ ⟨-, h0, hu, hl, hm, hr⟩ p
    have hl' := treeDomL_subset l _ s _ hl
    have hm' := treeDomL_subset m _ s _ hm
    have hr' := treeDomL_subset r _ s _ hr
    have hp : p = (tbNodeEquiv l m r).symm (tbNodeEquiv l m r p) := (Equiv.symm_apply_apply _ _).symm
    rcases hq : tbNodeEquiv l m r p with ⟨⟩ | q | q | q
    · rw [hp, hq]; exact ⟨h0.le, hu.le⟩
    · rw [hp, hq]; exact ⟨(hl' q).1, (hl' q).2.trans hu.le⟩
    · rw [hp, hq]; exact ⟨(hm' q).1, (hm' q).2.trans hu.le⟩
    · rw [hp, hq]; exact ⟨(hr' q).1, (hr' q).2.trans hu.le⟩

/-- The integrand of the time domain is integrable. -/
theorem integrable_treeDomL (T : TTree) (lp : Option TTree.Path) (β : TTree.Path → ℝ) (s u : ℝ) :
    Integrable ((treeDomL T lp s u).indicator (treePhase T β)) := by
  have hset : {τ : TB T → ℝ | ∀ p, τ p ∈ Icc 0 u} = Set.pi Set.univ fun _ => Icc 0 u := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have hbox : volume {τ : TB T → ℝ | ∀ p, τ p ∈ Icc 0 u} < ⊤ := by
    rw [hset, volume_pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => by simp
  have hmeas : MeasurableSet {τ : TB T → ℝ | ∀ p, τ p ∈ Icc 0 u} := by
    rw [hset]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hc : IntegrableOn (fun _ : TB T → ℝ => (1 : ℝ)) {τ : TB T → ℝ | ∀ p, τ p ∈ Icc 0 u} :=
    integrableOn_const hbox.ne
  refine Integrable.mono' ((integrable_indicator_iff hmeas).2 hc)
    (((continuous_treePhase T β).aestronglyMeasurable).indicator (measurableSet_treeDomL T lp s u))
    (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hτ : τ ∈ treeDomL T lp s u
  · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem (treeDomL_subset T lp s u hτ), norm_treePhase]
  · rw [Set.indicator_of_notMem hτ, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) τ

end Fubini

section Main

/-- The integrand of a node tree in terms of the root time and the subtree times. -/
theorem indicator_treeDomL_node (l m r : TTree) (lp : Option TTree.Path) (β : TTree.Path → ℝ)
    (s u : ℝ) (τ : TB (.node l m r) → ℝ) :
    (treeDomL (.node l m r) lp s u).indicator (treePhase (.node l m r) β) τ =
      (if LoneOK lp s u then 1 else 0) *
      ((Ioo 0 u).indicator (fun x => cexp (π * I * (β [] * x))) (tRoot τ) *
        ((treeDomL l (subLone lp 0) s (tRoot τ)).indicator (treePhase l fun p => β (0 :: p)) (tL τ) *
          (treeDomL m (subLone lp 1) s (tRoot τ)).indicator (treePhase m fun p => β (1 :: p)) (tM τ) *
          (treeDomL r (subLone lp 2) s (tRoot τ)).indicator (treePhase r fun p => β (2 :: p))
            (tR τ))) := by
  by_cases hL : LoneOK lp s u
  · rw [ite_eq_left hL, one_mul]
    by_cases h0 : tRoot τ ∈ Ioo 0 u
    · by_cases hl : tL τ ∈ treeDomL l (subLone lp 0) s (tRoot τ)
      · by_cases hm : tM τ ∈ treeDomL m (subLone lp 1) s (tRoot τ)
        · by_cases hr : tR τ ∈ treeDomL r (subLone lp 2) s (tRoot τ)
          · have hτ : τ ∈ treeDomL (.node l m r) lp s u := ⟨hL, h0.1, h0.2, hl, hm, hr⟩
            rw [Set.indicator_of_mem hτ, Set.indicator_of_mem h0, Set.indicator_of_mem hl,
              Set.indicator_of_mem hm, Set.indicator_of_mem hr, treePhase_node]
          · have hτ : τ ∉ treeDomL (.node l m r) lp s u := fun h => hr h.2.2.2.2.2
            rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hr, mul_zero, mul_zero]
        · have hτ : τ ∉ treeDomL (.node l m r) lp s u := fun h => hm h.2.2.2.2.1
          rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hm, mul_zero, zero_mul, mul_zero]
      · have hτ : τ ∉ treeDomL (.node l m r) lp s u := fun h => hl h.2.2.2.1
        rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hl, zero_mul, zero_mul, mul_zero]
    · have hτ : τ ∉ treeDomL (.node l m r) lp s u := fun h => h0 ⟨h.2.1, h.2.2.1⟩
      rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem h0, zero_mul]
  · have hτ : τ ∉ treeDomL (.node l m r) lp s u := fun h => hL h.1
    rw [ite_eq_right hL, zero_mul, Set.indicator_of_notMem hτ]

/-- **Fubini along a tree with a lone leaf** (DH21 (varat)): the integral over the time domain is the
iterated integral `treeIntL`. -/
theorem integral_treeDomL : ∀ (T : TTree) (lp : Option TTree.Path) (β : TTree.Path → ℝ) (s u : ℝ),
    0 ≤ u → ∫ τ : TB T → ℝ, (treeDomL T lp s u).indicator (treePhase T β) τ = treeIntL T lp β s u
  | .leaf, lp, β, s, u, _ => by
    have : IsEmpty (TB TTree.leaf) := ⟨fun p => not_mem_branching_leaf _ p.2⟩
    have hvol : (volume : Measure (TB TTree.leaf → ℝ)) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp
    have e : ∀ τ : TB TTree.leaf → ℝ, (treeDomL TTree.leaf lp s u).indicator (treePhase TTree.leaf β) τ =
        if LoneOK lp s u then 1 else 0 := fun τ => by
      by_cases h : LoneOK lp s u
      · rw [Set.indicator_of_mem (show τ ∈ treeDomL TTree.leaf lp s u from h), ite_eq_left h]
        simp [treePhase]
      · rw [Set.indicator_of_notMem (show τ ∉ treeDomL TTree.leaf lp s u from h), ite_eq_right h]
    simp_rw [e]
    rw [integral_const, measureReal_def, hvol]
    simp [treeIntL]
  | .node l m r, lp, β, s, u, hu => by
    set gl : ℝ → (TB l → ℝ) → ℂ := fun x =>
      (treeDomL l (subLone lp 0) s x).indicator (treePhase l fun p => β (0 :: p))
    set gm : ℝ → (TB m → ℝ) → ℂ := fun x =>
      (treeDomL m (subLone lp 1) s x).indicator (treePhase m fun p => β (1 :: p))
    set gr : ℝ → (TB r → ℝ) → ℂ := fun x =>
      (treeDomL r (subLone lp 2) s x).indicator (treePhase r fun p => β (2 :: p))
    set c : ℂ := if LoneOK lp s u then 1 else 0
    set f : ℝ → ℂ := (Ioo 0 u).indicator (fun x => cexp (π * I * (β [] * x)))
    set G : ℝ → ((TB l ⊕ (TB m ⊕ TB r)) → ℝ) → ℂ := fun x y =>
      c * (f x * (gl x (fun q => y (.inl q)) * gm x (fun q => y (.inr (.inl q))) *
        gr x (fun q => y (.inr (.inr q)))))
    have hF : ∀ τ : TB (.node l m r) → ℝ,
        (treeDomL (.node l m r) lp s u).indicator (treePhase (.node l m r) β) τ =
          G (tRoot τ) (fun z => τ ((tbNodeEquiv l m r).symm (.inr z))) := by
      intro τ
      rw [indicator_treeDomL_node]
      rfl
    simp_rw [hF]
    rw [← integral_reindex_pi (tbNodeEquiv l m r)]
    simp only [tRoot, Equiv.apply_symm_apply]
    rw [integral_sum_pi (fun p : (Unit → ℝ) × ((TB l ⊕ (TB m ⊕ TB r)) → ℝ) => G (p.1 ()) p.2)]
    have hint : Integrable (fun p : (Unit → ℝ) × ((TB l ⊕ (TB m ⊕ TB r)) → ℝ) => G (p.1 ()) p.2)
        ((volume : Measure (Unit → ℝ)).prod volume) := by
      have h0 := integrable_treeDomL (.node l m r) lp β s u
      have h1 := (((volume_measurePreserving_piCongrLeft (fun _ : Unit ⊕ (TB l ⊕ (TB m ⊕ TB r)) => ℝ)
        (tbNodeEquiv l m r)).symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h0
      have h2 := (((volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Unit ⊕ (TB l ⊕ (TB m ⊕ TB r)) => ℝ)).symm _).integrable_comp_emb
          (MeasurableEquiv.measurableEmbedding _)).2 h1
      refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply]
      rw [hF]
      simp only [tRoot]
      rfl
    rw [show ∫ p : (Unit → ℝ) × ((TB l ⊕ (TB m ⊕ TB r)) → ℝ), G (p.1 ()) p.2 =
      ∫ x : Unit → ℝ, ∫ y, G (x ()) y from integral_prod _ hint]
    have hin : ∀ x : ℝ, ∫ y : (TB l ⊕ (TB m ⊕ TB r)) → ℝ, G x y =
        c * (f x * ((∫ a, gl x a) * (∫ b, gm x b) * ∫ c, gr x c)) := by
      intro x
      simp only [G]
      rw [integral_const_mul, integral_const_mul]
      congr 2
      have h1 := integral_sum_pi_mul (gl x) (fun z : (TB m ⊕ TB r) → ℝ =>
        gm x (fun q => z (.inl q)) * gr x (fun q => z (.inr q)))
      have h2 := integral_sum_pi_mul (gm x) (gr x)
      simp only [mul_assoc] at h1 ⊢
      rw [h1, h2]
    simp_rw [hin]
    have hU := (volume_preserving_funUnique Unit ℝ).integral_comp' (fun x : ℝ =>
      c * (f x * ((∫ a, gl x a) * (∫ b, gm x b) * ∫ c, gr x c)))
    simp only [MeasurableEquiv.funUnique_apply] at hU
    rw [show (fun x : Unit → ℝ => c * (f (x ()) * ((∫ a, gl (x ()) a) * (∫ b, gm (x ()) b) *
      ∫ c, gr (x ()) c))) = fun x : Unit → ℝ => c * (f (x default) * ((∫ a, gl (x default) a) *
        (∫ b, gm (x default) b) * ∫ c, gr (x default) c)) from rfl, hU, integral_const_mul]
    rw [treeIntL, intervalIntegral.integral_of_le hu, integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioo]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ioo 0 u
    · simp only [f, Set.indicator_of_mem hx, gl, gm, gr]
      rw [integral_treeDomL l _ _ s x hx.1.le, integral_treeDomL m _ _ s x hx.1.le,
        integral_treeDomL r _ _ s x hx.1.le]
    · simp only [f, Set.indicator_of_notMem hx, zero_mul]

end Main

/-- **Fubini along a tree** (DH21 (defcoefa2) for one tree): the case without a lone leaf. -/
theorem integral_treeDomR (T : TTree) (β : TTree.Path → ℝ) (u : ℝ) (hu : 0 ≤ u) :
    ∫ τ : TB T → ℝ, (treeDomR T u).indicator (treePhase T β) τ = treeInt T β u := by
  rw [← treeDomL_none T 0 u, integral_treeDomL T none β 0 u hu, treeIntL_none]

end WaveTurbulence.MainCoef
