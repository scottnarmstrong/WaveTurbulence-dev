/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg2Dec

/-! # Rigid relocation of the upper block: the S-part (V5 Step 4b, step 4, WP-B part 3)

`spart_rigid`: the S-part `spart` of the twisted garden at the rigid image of the upper block, evaluated at a decoration
`x'` and a clock `u'`, is the S-part of the original garden at `x' ∘ naive` and the clock `u = u' ∘ eB`, provided the native
rows of `S` and the atom layers agree (the hypotheses `hC`, `hT`, `hl`, provided by `native_couple_eq` etc.).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hR : RigidAt P S b)

include hS hR in
/-- A realization node of `S` other than `a` is a child of an atom of `S` and is moved by the naive bijection like a child. -/
theorem naive_real (RS : CLRegionData G S a b) {x : GNode G.tree} (hx : x ∈ clRealizationNodes G S) (hxa : x ≠ a.toNode) :
    ∃ (v : GBranch G.tree) (i : Fin 3), v ∈ S ∧ x = v.child i ∧ naiveNodeEquiv G P x = (eB P v).child i := by
  obtain ⟨hn, hp⟩ := cl_realization_parent hS RS x hx hxa
  have hxv : x = (x.parent hn).child (x.1.2.getLast hn) := (Mole.parent_child_eq_node x hn).symm
  have key : ∀ (v : GBranch G.tree) (i : Fin 3), v ∈ S → x = v.child i →
      naiveNodeEquiv G P x = (eB P v).child i := by
    intro v i hv hxe
    by_cases hvb : v = b
    · subst hvb
      have hik : i = RS.kept := by
        by_contra hne
        have hreal := (mem_real_iff hS RS x).mp hx
        apply hreal.2.2 _ hne
        rw [hxe]
        exact isDesc_refl' _
      rw [hxe]
      exact hR.child_naive_real hv (hxe ▸ hx)
    · have hv' : v ∈ S.erase b := Finset.mem_erase.mpr ⟨hvb, hv⟩
      rw [hxe]
      exact hR.child_naive hv' _
  exact ⟨x.parent hn, x.1.2.getLast hn, hp, hxv, key _ _ hp hxv⟩

section Factors
variable {d : ℕ}

include hR in
theorem eps_rigid (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ)) :
    clRegionalEpsilon (unitTwistGarden G P) ((twistedAtoms G P S).erase (eB P b)) x' =
      clRegionalEpsilon G (S.erase b) (fun y => x' (naiveNodeEquiv G P y)) := by
  unfold clRegionalEpsilon
  refine (Finset.prod_equiv (eB P) (fun v => (mem_erase_twisted P v).symm) (fun v hv => ?_)).symm
  unfold epsBranch
  simp only [hR.child_naive hv]
  rfl

include hR in
theorem sign_omega_rigid (k' : GNode (unitTwistGarden G P).tree → Mom d) {v : GBranch G.tree} (hv : v ∈ S.erase b) :
    (((unitTwistGarden G P).sign (eB P v).toNode : ℤˣ) : ℤ) * omegaNode (unitTwistGarden G P) k' (eB P v) =
      ((G.sign v.toNode : ℤˣ) : ℤ) * omegaNode G (fun y => k' (naiveNodeEquiv G P y)) v := by
  have hl := hR.ne_lower (Finset.mem_of_mem_erase hv)
  have hs' : (unitTwistGarden G P).sign (eB P v).toNode = G.sign v.toNode := by
    rw [show (eB P v).toNode = (coreBranchEquiv G P v).toNode from rfl, coreBranchEquiv_sign, ite_eq_right hl]
  have a0 : naiveNodeEquiv G P v.toNode = (eB P v).toNode := naiveNodeEquiv_branch G P v
  rw [hs']
  congr 1
  unfold omegaNode
  simp only [hR.child_naive hv, a0]
  rfl

include hR in
theorem phase_rigid (L γ δ : ℝ) (k' : GNode (unitTwistGarden G P).tree → Mom d) (u' : GBranch (unitTwistGarden G P).tree → ℝ)
    (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S.erase b, u' (eB P v) = u v) :
    clRegionalPhase (unitTwistGarden G P) ((twistedAtoms G P S).erase (eB P b)) L γ δ k' u' =
      clRegionalPhase G (S.erase b) L γ δ (fun y => k' (naiveNodeEquiv G P y)) u := by
  unfold clRegionalPhase
  refine (Finset.prod_equiv (eB P) (fun v => (mem_erase_twisted P v).symm) (fun v hv => ?_)).symm
  rw [hu v hv]
  exact (phaseAtom_congr L γ δ _ _ _ _ _ (sign_omega_rigid P hR k' hv)).symm

end Factors

section Star
variable {d : ℕ}

include hS hR in
theorem parentClock_rigid (RS : CLRegionData G S a b) (t0 : ℝ) (u' : GBranch (unitTwistGarden G P).tree → ℝ)
    (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v) {x : GNode G.tree} (hx : x ∈ clRealizationNodes G S)
    (hxa : x ≠ a.toNode) :
    parentClock t0 u' (naiveNodeEquiv G P x) = parentClock t0 u x := by
  obtain ⟨v, i, hv, hxv, hn⟩ := naive_real P hS hR RS hx hxa
  rw [hn, hxv, parentClock_child, parentClock_child]
  exact hu v hv

include hS hR in
theorem domS_rigid (RS : CLRegionData G S a b) (lay : GBranch G.tree → ℕ)
    (lay' : GBranch (unitTwistGarden G P).tree → ℕ) (hlay : ∀ v ∈ S.erase a, lay' (eB P v) = lay v)
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v) :
    DomS lay' (twistedAtoms G P S) (eB P a) u' ↔ DomS lay S a u := by
  have hua : u' (eB P a) = u a := hu a hS.2.1
  unfold DomS
  constructor
  · intro h v hv
    have h1 := h (eB P v) ((mem_erase_twisted P (b := a) v).mpr hv)
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    have hpc : parentClock (u' (eB P a)) u' (eB P v).toNode = parentClock (u a) u v.toNode := by
      have := parentClock_rigid P hS hR RS (u' (eB P a)) u' u hu ((branch_mem_clRealizationNodes v).mpr hvS)
        (fun e => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective e))
      rw [naiveNodeEquiv_branch] at this
      rw [hua] at this ⊢
      exact this
    rw [hlay v hv, hu v hvS, hpc] at h1
    exact h1
  · intro h v' hv'
    obtain ⟨v, rfl⟩ := (eB P).surjective v'
    have hv : v ∈ S.erase a := (mem_erase_twisted P (b := a) v).mp hv'
    have h1 := h v hv
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    have hpc : parentClock (u' (eB P a)) u' (eB P v).toNode = parentClock (u a) u v.toNode := by
      have := parentClock_rigid P hS hR RS (u' (eB P a)) u' u hu ((branch_mem_clRealizationNodes v).mpr hvS)
        (fun e => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective e))
      rw [naiveNodeEquiv_branch] at this
      rw [hua] at this ⊢
      exact this
    rw [hlay v hv, hu v hvS, hpc]
    exact h1

end Star

section Pairs
variable {d : ℕ} (hG : G.IsPlain)

include hR in
theorem internal_iff_rigid (l : GLeaf G.tree) :
    Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S) (eL P l) ↔ Mole.IsInternalLeaf G S l := by
  have hl' : (reversePlacement G P).lower ∉ twistedAtoms G P S := fun h =>
    hR.lower_notMem ((mem_twistedAtoms G P S P.lower).mp h)
  by_cases h1 : l = P.retained
  · subst h1
    exact iff_of_false (not_internal_retained_of (reversePlacement G P) hl') (not_internal_retained_of P hR.lower_notMem)
  by_cases h2 : l = G.pair P.retained
  · subst h2
    refine iff_of_false ?_ (not_internal_pair_of P hR.lower_notMem)
    have := not_internal_pair_of (reversePlacement G P) hl'
    change ¬ Mole.IsInternalLeaf _ _ ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)) at this
    rw [unitTwistGarden_pair] at this
    exact this
  · exact ordinary_internal_iff G P l h1 h2

include hR in
theorem regional_tp_rigid (p : SourcePair G) :
    tp P hG p ∈ clRegionalPairs (unitTwistGarden_plain G P hG) (twistedAtoms G P S) ↔ p ∈ clRegionalPairs hG S := by
  have hpe : tp P hG p = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) := rfl
  rw [hpe]
  exact (mem_clRegionalPairs_of_leaf (unitTwistGarden G P) (hG := unitTwistGarden_plain G P hG) (U := twistedAtoms G P S)
    (eL P (p.firstLeaf hG))).trans ((internal_iff_rigid P hR (p.firstLeaf hG)).trans (mem_clRegionalPairs G).symm)

include hR in
theorem tp_first_rigid (p : SourcePair G) (hp : p ∈ clRegionalPairs hG S) :
    (tp P hG p).firstLeaf (unitTwistGarden_plain G P hG) = eL P (p.firstLeaf hG) ∧
    (tp P hG p).secondLeaf (unitTwistGarden_plain G P hG) = eL P (p.secondLeaf hG) := by
  have hint := (mem_clRegionalPairs G).mp hp
  have h1 : p.firstLeaf hG ≠ P.retained := fun h => not_internal_retained_of P hR.lower_notMem (h ▸ hint)
  have h2 : p.firstLeaf hG ≠ G.pair P.retained := fun h => not_internal_pair_of P hR.lower_notMem (h ▸ hint)
  have hs : nodeSign (unitTwistGarden G P).sig (eL P (p.firstLeaf hG)).1 = 1 := by
    have := coreLeafEquiv_sign G P (p.firstLeaf hG)
    simp only [coreLeafMultiplier, h1, h2, or_self, ite_false, one_mul] at this
    exact this.trans (sourcePair_first_sign G hG p)
  have hpe : tp P hG p = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) := rfl
  obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_pos (unitTwistGarden G P) (unitTwistGarden_plain G P hG) _ hs
  rw [hpe]
  refine ⟨hf, ?_⟩
  rw [hsec]
  exact (unitTwistGarden_pair G P (p.firstLeaf hG)).trans (congrArg (eL P) (pair_first_eq_second hG p))

end Pairs

section SPart
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG S, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ S.erase a, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hCi : ∀ p ∈ clRegionalPairs hG S, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ S.erase a, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
  (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)

include hS hR hC hT hCi hTi hlS in
/-- **The selected product is rigidly twist invariant** (ruling F2: the selection data are transported too). -/
theorem starProd_rigidS (RS : CLRegionData G S a b) (top : ℝ) (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v) :
    starProd D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) top x' u' =
      starProd D hG L γ δ F layer hLayer base S a top (fun y => x' (naiveNodeEquiv G P y)) u := by
  unfold starProd
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (Finset.prod_equiv (tp P hG) (fun p => (regional_tp_rigid P hR hG p).symm) (fun p hp => ?_)).symm
    obtain ⟨hf, hs⟩ := tp_first_rigid P hR hG p hp
    have hint := (mem_clRegionalPairs G).mp hp
    have hr1 : (p.firstLeaf hG).toNode ∈ clRealizationNodes G S := (leaf_mem_clRealizationNodes _).mpr hint
    have hr2 : (p.secondLeaf hG).toNode ∈ clRealizationNodes G S := by
      have := (Mole.internal_leaf_pair_iff G S (p.firstLeaf hG)).mpr hint
      rw [pair_first_eq_second hG p] at this
      exact (leaf_mem_clRealizationNodes _).mpr this
    have hl1 : (p.firstLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
    have hl2 : (p.secondLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
    have c1 := parentClock_rigid P hS hR RS top u' u hu hr1 hl1
    have c2 := parentClock_rigid P hS hR RS top u' u hu hr2 hl2
    have n1 : naiveNodeEquiv G P (p.firstLeaf hG).toNode = (eL P (p.firstLeaf hG)).toNode := naiveNodeEquiv_leaf G P _
    have n2 : naiveNodeEquiv G P (p.secondLeaf hG).toNode = (eL P (p.secondLeaf hG)).toNode := naiveNodeEquiv_leaf G P _
    obtain ⟨v1, i1, hv1, hx1, hn1⟩ := naive_real P hS hR RS hr1 hl1
    obtain ⟨v2, i2, hv2, hx2, hn2⟩ := naive_real P hS hR RS hr2 hl2
    have hq : ∀ i, Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) i =
        Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p i := by
      intro i
      fin_cases i
      · show Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) 0 =
          Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p 0
        rw [Flower.V5W.coupleRootParents_zero D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (tp P hG p)
            (eB P v1) i1 (by rw [hf, ← n1, hn1]),
          Flower.V5W.coupleRootParents_zero D hG layer hLayer rowSel.p p v1 i1 hx1, hlS v1 hv1]
      · show Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) 1 =
          Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p 1
        rw [Flower.V5W.coupleRootParents_one D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (tp P hG p)
            (eB P v2) i2 (by rw [hs, ← n2, hn2]),
          Flower.V5W.coupleRootParents_one D hG layer hLayer rowSel.p p v2 i2 hx2, hlS v2 hv2]
    rw [VineEst.selCoupleRow_congr L γ δ F D hG layer hLayer p D' (unitTwistGarden_plain G P hG) layer' hLayer'
      (tp P hG p) (hC p hp) (hCi p hp) hq, hf, hs]
    have c1' := (congrArg (parentClock top u') n1.symm).trans c1
    have c2' := (congrArg (parentClock top u') n2.symm).trans c2
    rw [c1', c2']
    have d1 : cosetDecoration (unitTwistGarden G P) L base x' (eL P (p.firstLeaf hG)).toNode =
        cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) (p.firstLeaf hG).toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) (congrArg x' n1.symm)
    rw [d1]
  · have hset : ∀ v, v ∈ S.erase a ↔ eB P v ∈ (twistedAtoms G P S).erase (eB P a) := fun v =>
      (mem_erase_twisted P (b := a) v).symm
    refine (Finset.prod_equiv (eB P) (fun v => hset v) (fun v hv => ?_)).symm
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    have hva : v ≠ a := (Finset.mem_erase.mp hv).1
    have hvn : v.toNode ≠ a.toNode := fun h => hva (Mole.branch_toNode_injective h)
    have c1 := parentClock_rigid P hS hR RS top u' u hu ((branch_mem_clRealizationNodes v).mpr hvS) hvn
    have c1' : parentClock top u' (eB P v).toNode = parentClock top u v.toNode :=
      (congrArg (parentClock top u') (naiveNodeEquiv_branch G P v).symm).trans c1
    have d1 : cosetDecoration (unitTwistGarden G P) L base x' (eB P v).toNode =
        cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) v.toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) (congrArg x' (naiveNodeEquiv_branch G P v).symm)
    obtain ⟨c, i, hc, hxc, hnc⟩ := naive_real P hS hR RS ((branch_mem_clRealizationNodes v).mpr hvS) hvn
    have hqT : Flower.V5W.treeRootParent rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        Flower.V5W.treeRootParent rowSel.p D hG layer hLayer v := by
      rw [Flower.V5W.treeRootParent_eq D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (eB P v) (eB P c) i
          ((naiveNodeEquiv_branch G P v).symm.trans hnc),
        Flower.V5W.treeRootParent_eq D hG layer hLayer rowSel.p v c i hxc, hlS c hc]
    rw [VineEst.selTreeRow_congr L γ δ F D hG layer hLayer v D' (unitTwistGarden_plain G P hG) layer' hLayer'
      (eB P v) (hT v hv) (hTi v hv) hqT, c1', hu v hvS, d1]

include hS hR hC hT in
/-- `starProd_rigidS` at the plain selector, with the original hypotheses (used by `Vine/C/VCRigid2`). -/
theorem starProd_rigid (RS : CLRegionData G S a b) (top : ℝ) (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v) :
    starProd (rowSel := VineEst.RowSel.plain) D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base
        (twistedAtoms G P S) (eB P a) top x' u' =
      starProd (rowSel := VineEst.RowSel.plain) D hG L γ δ F layer hLayer base S a top
        (fun y => x' (naiveNodeEquiv G P y)) u := by
  unfold starProd
  simp only [VineEst.selCoupleRow_plain, VineEst.selTreeRow_plain]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (Finset.prod_equiv (tp P hG) (fun p => (regional_tp_rigid P hR hG p).symm) (fun p hp => ?_)).symm
    obtain ⟨hf, hs⟩ := tp_first_rigid P hR hG p hp
    have hint := (mem_clRegionalPairs G).mp hp
    have hr1 : (p.firstLeaf hG).toNode ∈ clRealizationNodes G S := (leaf_mem_clRealizationNodes _).mpr hint
    have hr2 : (p.secondLeaf hG).toNode ∈ clRealizationNodes G S := by
      have := (Mole.internal_leaf_pair_iff G S (p.firstLeaf hG)).mpr hint
      rw [pair_first_eq_second hG p] at this
      exact (leaf_mem_clRealizationNodes _).mpr this
    have hl1 : (p.firstLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
    have hl2 : (p.secondLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
    have c1 := parentClock_rigid P hS hR RS top u' u hu hr1 hl1
    have c2 := parentClock_rigid P hS hR RS top u' u hu hr2 hl2
    have n1 : naiveNodeEquiv G P (p.firstLeaf hG).toNode = (eL P (p.firstLeaf hG)).toNode := naiveNodeEquiv_leaf G P _
    have n2 : naiveNodeEquiv G P (p.secondLeaf hG).toNode = (eL P (p.secondLeaf hG)).toNode := naiveNodeEquiv_leaf G P _
    rw [hf, hs, hC p hp]
    have c1' := (congrArg (parentClock top u') n1.symm).trans c1
    have c2' := (congrArg (parentClock top u') n2.symm).trans c2
    rw [c1', c2']
    have d1 : cosetDecoration (unitTwistGarden G P) L base x' (eL P (p.firstLeaf hG)).toNode =
        cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) (p.firstLeaf hG).toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) (congrArg x' n1.symm)
    rw [d1]
  · have hset : ∀ v, v ∈ S.erase a ↔ eB P v ∈ (twistedAtoms G P S).erase (eB P a) := fun v =>
      (mem_erase_twisted P (b := a) v).symm
    refine (Finset.prod_equiv (eB P) (fun v => hset v) (fun v hv => ?_)).symm
    have hvS : v ∈ S := Finset.mem_of_mem_erase hv
    have hva : v ≠ a := (Finset.mem_erase.mp hv).1
    have hvn : v.toNode ≠ a.toNode := fun h => hva (Mole.branch_toNode_injective h)
    have c1 := parentClock_rigid P hS hR RS top u' u hu ((branch_mem_clRealizationNodes v).mpr hvS) hvn
    have c1' : parentClock top u' (eB P v).toNode = parentClock top u v.toNode :=
      (congrArg (parentClock top u') (naiveNodeEquiv_branch G P v).symm).trans c1
    have d1 : cosetDecoration (unitTwistGarden G P) L base x' (eB P v).toNode =
        cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) v.toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) (congrArg x' (naiveNodeEquiv_branch G P v).symm)
    rw [hT v hv, c1', hu v hvS, d1]

include hS hR hC hT hCi hTi hlS in
/-- **The S-part is rigidly twist invariant.** -/
theorem spart_rigid (RS : CLRegionData G S a b) (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v)
    (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode) :
    spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b) x' u' =
      spart D hG L γ δ F layer hLayer base S a b (fun y => x' (naiveNodeEquiv G P y)) u := by
  unfold spart
  have hdom := domS_rigid P hS hR RS (fun v => layer (D.coreBranch hG v).toNode)
    (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode) (fun v hv => hl v hv) u' u hu
  have hua : u' (eB P a) = u a := hu a hS.2.1
  have heps := eps_rigid P hR x'
  have hph := phase_rigid P hR L γ δ (cosetDecoration (unitTwistGarden G P) L base x') u' u
    (fun v hv => hu v (Finset.mem_of_mem_erase hv))
  have hst := starProd_rigidS P hS hR hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hCi hTi hlS RS (u a) x' u' u hu
  rw [hua, hst] at *
  have hcd : cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) =
      fun y => cosetDecoration (unitTwistGarden G P) L base x' (naiveNodeEquiv G P y) := by
    funext y; unfold cosetDecoration; rfl
  rw [hcd, heps, hph]
  by_cases hd : DomS (fun v => layer (D.coreBranch hG v).toNode) S a u
  · simp only [hd, hdom.mpr hd]
  · have hd' : ¬ DomS (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode) (twistedAtoms G P S)
        (eB P a) u' := fun h => hd (hdom.mp h)
    simp only [hd, hd']

end SPart

end WaveTurbulence.VineEstS4
