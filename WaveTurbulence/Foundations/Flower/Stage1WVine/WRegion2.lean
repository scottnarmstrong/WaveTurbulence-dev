/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WRegion1

/-! # STAGE1W-VINE (T3): the regional product of the weighted slot family is the pinned selected product

* `clLocalStarProductG_slotFW`: the regional product of the frontier-weighted slot family is the crossing product of the
  coherent rows (`regionCross`) times the pinned `clLocalStarProductFW` (coherent rows: main's `KQstar`/`KTstar`;
  incoherent rows: `coupleLeavesTop`/`treeLeavesTop`).
* `regionWeightFW_eq_regionCross`: the pinned region multiplier `regionWeightFW … none` (the R135 bond product over the
  region darts whose row is coherent) IS the crossing product: each coherent row contributes its two darts, whose
  `topPsi` factors are its single crossing factor (supplement Lemma 5.1; the two darts of an LP bond carry the same
  momentum, a PC bond's child core lies below its parent core).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.LFTwist

section Cross
variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

open scoped Classical in
/-- **The crossing product of the coherent regional rows** of a block `(U, a)` at a decoration `x`. -/
def regionCross (p : ℕ) (g : Mom d → ℂ) (U : Finset (GBranch S.tree)) (a : GBranch S.tree) (L : ℝ) (base : Mom d)
    (x : GNode S.tree → (Fin d → ℤ)) : ℂ :=
  (∏ pr ∈ clRegionalPairs hS U, if coupleIncoh D hS layer hLayer pr = 0 then
      coupleCross p g (coupleRootParents p D hS layer hLayer pr 0) (coupleRootParents p D hS layer hLayer pr 1)
        (cosetDecoration S L base x (pr.firstLeaf hS).toNode) else 1) *
    ∏ v ∈ U.erase a, if treeIncoh D hS layer hLayer v = 0 then
      treeCross p g (treeRootParent p D hS layer hLayer v) (layer (D.coreBranch hS v).toNode)
        (cosetDecoration S L base x v.toNode) else 1

theorem coreLayer_le_treeRootParent (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    (hlay : ∀ x, layer x ≤ p) (v : GBranch S.tree) (hinc : treeIncoh D hS layer hLayer v = 0) :
    layer (D.coreBranch hS v).toNode ≤ treeRootParent p D hS layer hLayer v := by
  have hcoh := tree_coherent_at D hS layer hLayer p hcan v hinc
  rw [← treeRootParent_eq_clkLayer D hS layer hLayer p v] at hcoh
  have hq' : clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr v) 1) =
      layer (D.coreBranch hS v).toNode := by simp [argSrc, clkLayer]
  rw [hq'] at hcoh
  obtain ⟨_, hX, _, H, a, _, _, _, _, _, _, hlone, hlay'⟩ := hcoh
  let y : GNode (nativeChainLayered D hS layer hLayer v).garden.tree := ⟨(0, (D.tree v).lonePath), by
    show (D.tree v).lonePath ∈ ((nativeChainLayered D hS layer hLayer v).garden.tree 0).nodes
    rw [hX.1]; exact Links.lonePath_mem_plug _ _ _⟩
  have h1 : (nativeChainLayered D hS layer hLayer v).layer y = layer (D.coreBranch hS v).toNode :=
    (hlay' y).trans hlone
  have h2 := node_layer_le_rootV (nativeChainLayered D hS layer hLayer v) y
  have h3 := layer_le_parentLayer (layeredReconstruction D hS layer hLayer) p hlay
    (chainContextNode D hS v (GNode.root (nativeChainLayered D hS layer hLayer v).garden.tree 0))
  rw [← h1]
  exact h2.trans h3

variable (L γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (gT : Fin w → Mom d → ℂ)

/-- **The regional product of the frontier-weighted slot family** is the crossing product times the pinned
`clLocalStarProductFW` (with the unit's layer profile). -/
theorem clLocalStarProductG_slotFW (u : CLBlock S) (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    (hlay : ∀ x, layer x ≤ p) (R : CLRegionData S u.atoms u.upper u.lower) (base : Mom d)
    (x : GNode S.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProductG hS R (slotFW D hS layer hLayer L γ δ h p gT) L base x t τ =
      regionCross D hS layer hLayer p (gT u.upper.1.1) u.atoms u.upper L base x *
        clLocalStarProductFW p (gT u.upper.1.1) D hS R L γ δ (fun q => h q u.upper.1.1 u.upper.1.1) layer hLayer
          base x t τ := by
  classical
  unfold clLocalStarProductG starProdG regionCross
  simp only [clLocalStarProductFW]
  unfold clInteriorBranches
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun pr hpr => ?_
    rw [slotFW_regional_couple D hS layer hLayer L γ δ h p gT u hpr]
    simp only [pairTimes, Fin.isValue, ↓reduceIte, one_ne_zero]
    by_cases hc : coupleIncoh D hS layer hLayer pr = 0
    · rw [if_pos hc, if_pos hc, coupleLeavesTop_coherent D hS layer hLayer p hcan hlay pr hc]
    · rw [if_neg hc, if_neg hc, one_mul]
  · refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨hva, hvU⟩ := Finset.mem_erase.mp hv
    rw [slotFW_regional_chain D hS layer hLayer L γ δ h p gT u hvU hva]
    simp only [chainTimes, Fin.isValue, ↓reduceIte, one_ne_zero]
    by_cases hc : treeIncoh D hS layer hLayer v = 0
    · rw [if_pos hc, if_pos hc, treeLeavesTop_coherent D hS layer hLayer p hcan hlay v hc]
    · rw [if_neg hc, if_neg hc, one_mul]

end Cross

/-! ## The region multiplier is the crossing product -/

section Darts
variable {w d : ℕ} {ι : Type*}

theorem stateCoreLayer_eq (X : FamilyReconstruction w ι) (c : GBranch X.skeleton.tree) :
    stateCoreLayer X c = stateLayer X (X.data.coreBranch X.plain c).toNode := by
  unfold stateCoreLayer
  rw [← stateLayer_spec X]
  exact Links.layerAt_node (layeredReconstruction X.data X.plain (stateLayer X) (stateLayer_isLayering X))
    (X.data.coreBranch X.plain c).toNode

/-- The parent branch of a nonroot node, as the node below which it is a child. -/
theorem toNode_eq_child_parent {G : Garden w} (x : GNode G.tree) (hn : x.1.2 ≠ []) :
    x = (x.parent hn).child (x.1.2.getLast hn) :=
  (Reg.Skeleton.child_parent x hn).symm

theorem topPsi_pair_PC (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (hq : q' ≤ q) (k : Mom d) :
    topPsi p g q' q k * topPsi p g q q' k = treeCross p g q q' k := by
  unfold topPsi treeCross
  split_ifs <;> first | (exfalso; omega) | ring

theorem topPsi_pair_LP (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (k : Mom d) :
    topPsi p g q' q k * topPsi p g q q' k = coupleCross p g q q' k := by
  unfold topPsi coupleCross
  split_ifs <;> first | (exfalso; omega) | ring

open scoped Classical in
/-- **The R135 multiplier of the pinned kernel is the crossing product of the coherent rows.** -/
theorem regionWeightFW_eq_regionCross (X : FamilyReconstruction w ι) (u : CLBlock X.skeleton) (p : ℕ)
    (g : Mom d → ℂ) (L : ℝ) (base : Mom d)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction X.data X.plain (stateLayer X) (stateLayer_isLayering X)))
    (hlay : ∀ x, stateLayer X x ≤ p) (R : CLRegionData X.skeleton u.atoms u.upper u.lower) (β : Fin 4 → Mom d)
    (κ : CLLocalDecoration R L base β) :
    regionWeightFW p g none L base X u.atoms u.upper (clExtendIndices R κ.1) =
      regionCross X.data X.plain (stateLayer X) (stateLayer_isLayering X) p g u.atoms u.upper L base
        (clExtendIndices R κ.1) := by
  set f : GardenDart X.skeleton → ℂ := fun y =>
    if nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0 then
      topPsi p g (stateCoreLayer X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y))) (stateCoreLayer X (X.skeleton.molecule.atom y))
        (cosetDecoration X.skeleton L base (clExtendIndices R κ.1) (Mole.dartNode X.skeleton y)) else 1 with hf
  have hnw : VineSpaceK.nodeWeight (topFilterWeight (d := d) none) L base u.upper (clExtendIndices R κ.1) = 1 := by
    simp [VineSpaceK.nodeWeight, topFilterWeight]
  unfold regionWeightFW
  rw [hnw, mul_one]
  change ∏ y ∈ Finset.univ.filter (X.skeleton.molecule.InGroup u.atoms), f y = _
  rw [Finset.prod_filter, Fintype.prod_sum_type]
  unfold regionCross
  rw [mul_comm]
  congr 1
  · -- LP darts ↔ regional pairs
    set lpTerm : GLeaf X.skeleton.tree → ℂ := fun l =>
      if h : X.skeleton.mark l = none ∧ l.1.2 ≠ [] ∧ (X.skeleton.pair l).1.2 ≠ [] then f (.inr ⟨l, h⟩) else 1 with hlp
    have e1 : ∏ ℓ : {ℓ : GLeaf X.skeleton.tree // X.skeleton.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (X.skeleton.pair ℓ).1.2 ≠ []},
        (if X.skeleton.molecule.InGroup u.atoms (Sum.inr ℓ) then f (Sum.inr ℓ) else 1) =
        ∏ l ∈ Finset.univ.filter (Mole.IsInternalLeaf X.skeleton u.atoms), lpTerm l := by
      set F : GLeaf X.skeleton.tree → ℂ := fun l => if Mole.IsInternalLeaf X.skeleton u.atoms l then lpTerm l else 1
        with hF
      have step1 : ∀ ℓ : {ℓ : GLeaf X.skeleton.tree // X.skeleton.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (X.skeleton.pair ℓ).1.2 ≠ []},
          (if X.skeleton.molecule.InGroup u.atoms (Sum.inr ℓ) then f (Sum.inr ℓ) else 1) = F ℓ.1 := by
        intro ℓ
        have hiff : X.skeleton.molecule.InGroup u.atoms (Sum.inr ℓ) ↔ Mole.IsInternalLeaf X.skeleton u.atoms ℓ.1 :=
          ⟨fun h => ⟨ℓ.2.1, ℓ.2.2.1, ℓ.2.2.2, h⟩, fun ⟨_, _, _, h⟩ => h⟩
        simp only [hF]
        by_cases hg : X.skeleton.molecule.InGroup u.atoms (Sum.inr ℓ)
        · rw [if_pos hg, if_pos (hiff.mp hg)]
          have hl : lpTerm ℓ.1 = f (Sum.inr ℓ) := by
            simp only [hlp]
            exact dif_pos ℓ.2
          exact hl.symm
        · rw [if_neg hg, if_neg (fun h => hg (hiff.mpr h))]
      calc _ = ∏ ℓ : {ℓ : GLeaf X.skeleton.tree // X.skeleton.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (X.skeleton.pair ℓ).1.2 ≠ []},
            F ℓ.1 := Finset.prod_congr rfl fun ℓ _ => step1 ℓ
        _ = ∏ l ∈ Finset.univ.filter (fun l : GLeaf X.skeleton.tree =>
              X.skeleton.mark l = none ∧ l.1.2 ≠ [] ∧ (X.skeleton.pair l).1.2 ≠ []), F l :=
            (Finset.prod_subtype _ (fun l => by simp) F).symm
        _ = ∏ l, if (X.skeleton.mark l = none ∧ l.1.2 ≠ [] ∧ (X.skeleton.pair l).1.2 ≠ []) then F l else 1 :=
            Finset.prod_filter _ _
        _ = ∏ l, if Mole.IsInternalLeaf X.skeleton u.atoms l then lpTerm l else 1 := by
            refine Finset.prod_congr rfl fun l _ => ?_
            simp only [hF]
            by_cases hl : X.skeleton.mark l = none ∧ l.1.2 ≠ [] ∧ (X.skeleton.pair l).1.2 ≠ []
            · rw [if_pos hl]
            · rw [if_neg hl]
              have : ¬ Mole.IsInternalLeaf X.skeleton u.atoms l := fun ⟨hm, hn, hp, _⟩ => hl ⟨hm, hn, hp⟩
              rw [if_neg this]
        _ = _ := (Finset.prod_filter _ _).symm
    rw [e1]
    have hmaps : ∀ l ∈ Finset.univ.filter (Mole.IsInternalLeaf X.skeleton u.atoms),
        pairOfLeaf X.skeleton X.plain l ∈ clRegionalPairs X.plain u.atoms := by
      intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      unfold clRegionalPairs
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases pairOfLeaf_first_or_partner X.skeleton X.plain l with h1 | h1
      · rw [h1]; exact hl'
      · rw [h1]; exact (Mole.internal_leaf_pair_iff X.skeleton u.atoms l).mpr hl'
    rw [← Finset.prod_fiberwise_of_maps_to hmaps]
    refine Finset.prod_congr rfl fun pr hpr => ?_
    have hf1 : Mole.IsInternalLeaf X.skeleton u.atoms (pr.firstLeaf X.plain) := (Finset.mem_filter.mp hpr).2
    have hf2 := (second_internal_iff X.plain u.atoms pr).mpr hf1
    have hpart : X.skeleton.pair (pr.firstLeaf X.plain) = pr.secondLeaf X.plain := sourcePair_partner X.skeleton _ _ (Or.inl pr.2)
    have hne : pr.firstLeaf X.plain ≠ pr.secondLeaf X.plain := by
      intro he
      have h1 : X.skeleton.pair (pr.firstLeaf X.plain) = pr.firstLeaf X.plain := hpart.trans he.symm
      exact ((X.skeleton.pair_eq_iff _).mp h1) (X.plain _)
    have hfib : (Finset.univ.filter (Mole.IsInternalLeaf X.skeleton u.atoms)).filter
        (fun l => pairOfLeaf X.skeleton X.plain l = pr) = {pr.firstLeaf X.plain, pr.secondLeaf X.plain} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hl⟩
        have := eq_or_pair_of_pairOfLeaf (S := X.skeleton) X.plain (l := l) (r := pr.firstLeaf X.plain)
          (hl.trans (pairOfLeaf_firstLeaf X.skeleton X.plain pr).symm)
        rcases this with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (h1.trans hpart)
      · rintro (h1 | h1)
        · rw [h1]; exact ⟨hf1, pairOfLeaf_firstLeaf X.skeleton X.plain pr⟩
        · rw [h1]; exact ⟨hf2, pairOfLeaf_secondLeaf X.skeleton X.plain pr⟩
    rw [hfib, Finset.prod_pair hne]
    have hf1' := hf1
    obtain ⟨hm1, hn1, hp1, _⟩ := hf1
    obtain ⟨hm2, hn2, hp2, _⟩ := hf2
    have ht1 : lpTerm (pr.firstLeaf X.plain) = f (.inr ⟨pr.firstLeaf X.plain, hm1, hn1, hp1⟩) := by
      simp only [hlp]
      rw [dif_pos ⟨hm1, hn1, hp1⟩]
    have ht2 : lpTerm (pr.secondLeaf X.plain) = f (.inr ⟨pr.secondLeaf X.plain, hm2, hn2, hp2⟩) := by
      simp only [hlp]
      rw [dif_pos ⟨hm2, hn2, hp2⟩]
    rw [ht1, ht2]
    -- the two darts of the LP bond
    set v1 := (pr.firstLeaf X.plain).toNode.parent hn1 with hv1
    set v2 := (pr.secondLeaf X.plain).toNode.parent hn2 with hv2
    have hrow1 : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X)
        (pr.firstLeaf X.plain).toNode = coupleIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) pr := by
      rw [nodeRowIncoh_leaf, pairOfLeaf_firstLeaf]
    have hrow2 : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X)
        (pr.secondLeaf X.plain).toNode = coupleIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) pr := by
      rw [nodeRowIncoh_leaf, pairOfLeaf_secondLeaf]
    have hq0 : coupleRootParents p X.data X.plain (stateLayer X) (stateLayer_isLayering X) pr 0 =
        stateCoreLayer X v1 := by
      rw [stateCoreLayer_eq]
      exact coupleRootParents_zero X.data X.plain (stateLayer X) (stateLayer_isLayering X) p pr v1 _
        (toNode_eq_child_parent _ hn1)
    have hq1 : coupleRootParents p X.data X.plain (stateLayer X) (stateLayer_isLayering X) pr 1 =
        stateCoreLayer X v2 := by
      rw [stateCoreLayer_eq]
      exact coupleRootParents_one X.data X.plain (stateLayer X) (stateLayer_isLayering X) p pr v2 _
        (toNode_eq_child_parent _ hn2)
    have hk : cosetDecoration X.skeleton L base (clExtendIndices R κ.1) (pr.secondLeaf X.plain).toNode =
        cosetDecoration X.skeleton L base (clExtendIndices R κ.1) (pr.firstLeaf X.plain).toNode := by
      unfold cosetDecoration
      rw [← hpart, ← κ.2.2.1 _ hf1']
    have hatom1 : X.skeleton.molecule.atom (Sum.inr ⟨pr.firstLeaf X.plain, hm1, hn1, hp1⟩) = v1 := rfl
    have key : ∀ (l l' : GLeaf X.skeleton.tree) (_ : l = l') (h : l.1.2 ≠ []) (h' : l'.1.2 ≠ []),
        l.toNode.parent h = l'.toNode.parent h' := by
      intro l l' e h h'; subst e; rfl
    have hmate1 : X.skeleton.molecule.atom (X.skeleton.molecule.mate (Sum.inr ⟨pr.firstLeaf X.plain, hm1, hn1, hp1⟩)) = v2 :=
      key _ _ hpart hp1 hn2
    have hatom2 : X.skeleton.molecule.atom (Sum.inr ⟨pr.secondLeaf X.plain, hm2, hn2, hp2⟩) = v2 := rfl
    have hmate2 : X.skeleton.molecule.atom (X.skeleton.molecule.mate (Sum.inr ⟨pr.secondLeaf X.plain, hm2, hn2, hp2⟩)) = v1 := by
      have hpart' : X.skeleton.pair (pr.secondLeaf X.plain) = pr.firstLeaf X.plain := by rw [← hpart, X.skeleton.pair_pair]
      exact key _ _ hpart' hp2 hn1
    simp only [hf, Mole.dartNode]
    simp only [hrow1, hrow2, hatom1, hmate1, hatom2, hmate2, hk, hq0, hq1]
    by_cases hc : coupleIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) pr = 0
    · simp only [if_pos hc]
      exact topPsi_pair_LP p g _ _ _
    · simp only [if_neg hc, one_mul]
  · -- PC darts ↔ interior branches
    set pcTerm : GBranch X.skeleton.tree → ℂ := fun v =>
      if hv : v.1.2 ≠ [] then f (.inl (⟨v, hv⟩, true)) * f (.inl (⟨v, hv⟩, false)) else 1 with hpc
    set Q : GBranch X.skeleton.tree → Prop := fun v => ∃ hv : v.1.2 ≠ [], v ∈ u.atoms ∧ v.toNode.parent hv ∈ u.atoms with hQ
    have e1 : ∏ cb : {c : GBranch X.skeleton.tree // c.1.2 ≠ []} × Bool,
        (if X.skeleton.molecule.InGroup u.atoms (Sum.inl cb) then f (Sum.inl cb) else 1) =
        ∏ v ∈ Finset.univ.filter Q, pcTerm v := by
      set F : GBranch X.skeleton.tree → ℂ := fun v => if Q v then pcTerm v else 1 with hF
      have step1 : ∀ c : {c : GBranch X.skeleton.tree // c.1.2 ≠ []},
          ∏ b : Bool, (if X.skeleton.molecule.InGroup u.atoms (Sum.inl (c, b)) then f (Sum.inl (c, b)) else 1) =
            F c.1 := by
        intro c
        have hiffT : X.skeleton.molecule.InGroup u.atoms (Sum.inl (c, true)) ↔ Q c.1 := by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨c.2, h2, h1⟩
          · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
        have hiffF : X.skeleton.molecule.InGroup u.atoms (Sum.inl (c, false)) ↔ Q c.1 := by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨c.2, h1, h2⟩
          · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
        rw [Fintype.prod_bool]
        simp only [hF]
        by_cases hq : Q c.1
        · rw [if_pos (hiffT.mpr hq), if_pos (hiffF.mpr hq), if_pos hq]
          have hpcc : pcTerm c.1 = f (.inl (c, true)) * f (.inl (c, false)) := by
            simp only [hpc]
            exact dif_pos c.2
          exact hpcc.symm
        · rw [if_neg (fun h => hq (hiffT.mp h)), if_neg (fun h => hq (hiffF.mp h)), if_neg hq, one_mul]
      calc _ = ∏ c : {c : GBranch X.skeleton.tree // c.1.2 ≠ []}, F c.1 := by
            rw [Fintype.prod_prod_type]
            exact Finset.prod_congr rfl fun c _ => step1 c
        _ = ∏ v ∈ Finset.univ.filter (fun v : GBranch X.skeleton.tree => v.1.2 ≠ []), F v :=
            (Finset.prod_subtype _ (fun v => by simp) F).symm
        _ = ∏ v, if v.1.2 ≠ [] then F v else 1 := Finset.prod_filter _ _
        _ = ∏ v, if Q v then pcTerm v else 1 := by
            refine Finset.prod_congr rfl fun v _ => ?_
            simp only [hF]
            by_cases hv : v.1.2 ≠ []
            · rw [if_pos hv]
            · rw [if_neg hv]
              have : ¬ Q v := fun ⟨h, _⟩ => hv h
              rw [if_neg this]
        _ = _ := (Finset.prod_filter _ _).symm
    rw [e1]
    have hset : Finset.univ.filter Q = u.atoms.erase u.upper := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hv, hvU, hpU⟩
        refine ⟨fun he => ?_, hvU⟩
        subst he
        exact upper_parent_not_mem u hv hpU
      · rintro ⟨hva, hvU⟩
        obtain ⟨hn, hpU⟩ := real_parent u ((branch_real_iff u v).mpr hvU)
          (fun he => hva (Subtype.ext (congrArg (fun y : GNode X.skeleton.tree => y.1) he)))
        exact ⟨hn, hvU, hpU⟩
    rw [hset]
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨hva, hvU⟩ := Finset.mem_erase.mp hv
    obtain ⟨hn, -⟩ := real_parent u ((branch_real_iff u v).mpr hvU)
      (fun he => hva (Subtype.ext (congrArg (fun y : GNode X.skeleton.tree => y.1) he)))
    set c := v.toNode.parent hn with hc
    have hrow : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) v.toNode =
        treeIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) v := nodeRowIncoh_branch _ _ _ _ v
    have hq : treeRootParent p X.data X.plain (stateLayer X) (stateLayer_isLayering X) v = stateCoreLayer X c := by
      rw [stateCoreLayer_eq]
      exact treeRootParent_eq X.data X.plain (stateLayer X) (stateLayer_isLayering X) p v c _
        (toNode_eq_child_parent _ hn)
    have hq' : stateLayer X (X.data.coreBranch X.plain v).toNode = stateCoreLayer X v := (stateCoreLayer_eq X v).symm
    have hpcv : pcTerm v = f (.inl (⟨v, hn⟩, true)) * f (.inl (⟨v, hn⟩, false)) := by
      simp only [hpc]
      exact dif_pos hn
    rw [hpcv]
    simp only [hf, Mole.dartNode]
    have hat1 : X.skeleton.molecule.atom (Sum.inl (⟨v, hn⟩, true)) = c := rfl
    have hat2 : X.skeleton.molecule.atom (Sum.inl (⟨v, hn⟩, false)) = v := rfl
    have hm1 : X.skeleton.molecule.atom (X.skeleton.molecule.mate (Sum.inl (⟨v, hn⟩, true))) = v := rfl
    have hm2 : X.skeleton.molecule.atom (X.skeleton.molecule.mate (Sum.inl (⟨v, hn⟩, false))) = c := rfl
    simp only [hat1, hat2, hm1, hm2, hrow, hq, hq']
    by_cases hinc : treeIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) v = 0
    · simp only [if_pos hinc]
      have hle := coreLayer_le_treeRootParent X.data X.plain (stateLayer X) (stateLayer_isLayering X) p hcan hlay v hinc
      rw [hq, hq'] at hle
      exact topPsi_pair_PC p g _ _ hle _
    · simp only [if_neg hinc, one_mul]

end Darts

end WaveTurbulence.Flower.Stage1WVine
