/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.WeightN
public import WaveTurbulence.Foundations.Flower.V5WB.Sel

/-! # V5W-B-WORLD B4: the rows of a CL region are its bonds

In a CL block `U` (top joint `a`), the PC darts with both ends in `U` are the two darts of the PC bond of each interior
branch `v ∈ U \ {a}` (every such branch has its parent in `U`, `cl_realization_parent`; the parent of `a` is outside),
and the LP darts with both ends in `U` are the two darts of the LP bond of each regional pair (`IsInternalLeaf`).  Hence
the product over the region darts of the per-node normalization factor `nodeNorm` (the dart part of `ΨX` on an
incoherent row) is the row normalization `rowNorm` of the region (`prod_nodeNorm_regionDarts`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts)
open WaveTurbulence.Flower.V5W (nodeRowIncoh nodeRowIncoh_branch nodeRowIncoh_leaf coupleIncoh treeIncoh)

section
variable {w : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ)
  (hLayer : IsLayering (D.garden hG) layer) (c : ℝ)

/-- The per-node factor of the row normalization (`1` on a coherent row, `c ^ (e/2)` on an incoherent one). -/
def nodeNorm (x : GNode G.tree) : ℝ :=
  if nodeRowIncoh D hG layer hLayer x = 0 then 1 else c ^ ((nodeRowExp D hG layer hLayer x : ℝ) / 2)

theorem rpow_half_mul_self {c : ℝ} (hc : 0 ≤ c) (e : ℕ) (he : 0 < e) :
    c ^ ((e : ℝ) / 2) * c ^ ((e : ℝ) / 2) = c ^ e := by
  have hpos : (e : ℝ) / 2 + (e : ℝ) / 2 ≠ 0 := by
    have : (0 : ℝ) < e := by exact_mod_cast he
    positivity
  rw [← Real.rpow_add' hc hpos, show (e : ℝ) / 2 + (e : ℝ) / 2 = ((e : ℕ) : ℝ) by ring, Real.rpow_natCast]

theorem nodeNorm_branch_sq (hc : 0 ≤ c) (v : GBranch G.tree) :
    nodeNorm D hG layer hLayer c v.toNode * nodeNorm D hG layer hLayer c v.toNode = treeNorm c D hG layer hLayer v := by
  unfold nodeNorm treeNorm
  rw [nodeRowIncoh_branch, nodeRowExp_branch]
  split_ifs
  · ring
  · exact rpow_half_mul_self hc _ (by omega)

theorem nodeNorm_pair (hc : 0 ≤ c) (q : SourcePair G) :
    nodeNorm D hG layer hLayer c (q.firstLeaf hG).toNode * nodeNorm D hG layer hLayer c (q.secondLeaf hG).toNode =
      coupleNorm c D hG layer hLayer q := by
  unfold nodeNorm coupleNorm
  rw [nodeRowIncoh_leaf, nodeRowIncoh_leaf, nodeRowExp_leaf, nodeRowExp_leaf, pairOfLeaf_firstLeaf,
    pairOfLeaf_secondLeaf]
  split_ifs
  · ring
  · exact rpow_half_mul_self hc _ (by omega)

/-- The leaf of a source pair on a side. -/
def sideLeaf (q : SourcePair G) (s : Bool) : GLeaf G.tree := if s then q.firstLeaf hG else q.secondLeaf hG

theorem first_ne_second (q : SourcePair G) (hm : G.mark (q.firstLeaf hG) = none) :
    q.firstLeaf hG ≠ q.secondLeaf hG := by
  intro h
  have h2 : G.pair (q.firstLeaf hG) = q.firstLeaf hG := (VineEstS4.pair_first_eq_second hG q).trans h.symm
  exact (G.pair_eq_iff _).1 h2 hm

theorem pairOfLeaf_sideLeaf (q : SourcePair G) (s : Bool) : pairOfLeaf G hG (sideLeaf hG q s) = q := by
  unfold sideLeaf
  cases s
  · exact pairOfLeaf_secondLeaf G hG q
  · exact pairOfLeaf_firstLeaf G hG q

theorem internal_sideLeaf {U : Finset (GBranch G.tree)} {q : SourcePair G} (hq : q ∈ clRegionalPairs hG U) (s : Bool) :
    Mole.IsInternalLeaf G U (sideLeaf hG q s) := by
  have h1 := (mem_clRegionalPairs G).mp hq
  unfold sideLeaf
  cases s
  · have := (Mole.internal_leaf_pair_iff G U (q.firstLeaf hG)).mpr h1
    rwa [VineEstS4.pair_first_eq_second hG q] at this
  · exact h1

/-- **The rows of a CL region are its bonds**: the product of the node factors over the region darts is the row
normalization. -/
theorem prod_nodeNorm_regionDarts (hc : 0 ≤ c) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    ∏ y ∈ regionDarts G U, nodeNorm D hG layer hLayer c (Mole.dartNode G y) = rowNorm c D hG R layer hLayer := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (regionDarts G U) (fun y => y.isLeft = true)]
  unfold rowNorm
  rw [mul_comm]
  congr 1
  · -- the LP darts: two per regional pair
    have hR : ∏ q ∈ clRegionalPairs hG U, coupleNorm c D hG layer hLayer q =
        ∏ x ∈ (clRegionalPairs hG U) ×ˢ (Finset.univ : Finset Bool),
          nodeNorm D hG layer hLayer c (sideLeaf hG x.1 x.2).toNode := by
      rw [Finset.prod_product]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [Fintype.prod_bool]
      exact (nodeNorm_pair D hG layer hLayer c hc q).symm
    rw [hR]
    symm
    refine Finset.prod_bij (fun x hx => (.inr ⟨sideLeaf hG x.1 x.2,
        (internal_sideLeaf hG (Finset.mem_product.mp hx).1 x.2).fst,
        (internal_sideLeaf hG (Finset.mem_product.mp hx).1 x.2).snd.fst,
        (internal_sideLeaf hG (Finset.mem_product.mp hx).1 x.2).snd.snd.fst⟩ : GardenDart G)) ?_ ?_ ?_ ?_
    · intro x hx
      refine Finset.mem_filter.mpr ⟨mem_regionDarts.mpr ?_, by simp⟩
      exact (internal_sideLeaf hG (Finset.mem_product.mp hx).1 x.2).snd.snd.snd
    · intro x hx y hy h
      simp only [Sum.inr.injEq, Subtype.mk.injEq] at h
      have hq : x.1 = y.1 := by
        rw [← pairOfLeaf_sideLeaf hG x.1 x.2, ← pairOfLeaf_sideLeaf hG y.1 y.2, h]
      have hm := (internal_sideLeaf hG (Finset.mem_product.mp hx).1 true).fst
      refine Prod.ext hq ?_
      rcases x with ⟨q, s⟩
      rcases y with ⟨q', s'⟩
      dsimp only at hq h ⊢
      subst hq
      have hne := first_ne_second hG q hm
      cases s <;> cases s' <;> simp_all [sideLeaf]
    · intro y hy
      obtain ⟨hyU, hyl⟩ := Finset.mem_filter.mp hy
      rcases y with ⟨cc, s⟩ | l
      · exact absurd hyl (by simp)
      · have hint : Mole.IsInternalLeaf G U l.1 := ⟨l.2.1, l.2.2.1, l.2.2.2, mem_regionDarts.mp hyU⟩
        have hq := (mem_clRegionalPairs_of_leaf G (hG := hG) (U := U) l.1).mpr hint
        have hside : sideLeaf hG (pairOfLeaf G hG l.1)
            (decide ((pairOfLeaf G hG l.1).firstLeaf hG = l.1)) = l.1 := by
          unfold sideLeaf
          by_cases h : (pairOfLeaf G hG l.1).firstLeaf hG = l.1
          · simp [h]
          · simp only [h, decide_false]
            rcases pairOfLeaf_first_or_partner G hG l.1 with h' | h'
            · exact absurd h' h
            · rw [← VineEstS4.pair_first_eq_second hG, h', G.pair_pair]
              simp
        refine ⟨(pairOfLeaf G hG l.1, decide ((pairOfLeaf G hG l.1).firstLeaf hG = l.1)),
          Finset.mem_product.mpr ⟨hq, Finset.mem_univ _⟩, ?_⟩
        congr 1
        exact Subtype.ext hside
    · intro x _
      rfl
  · -- the PC darts: two per interior branch
    have hpar : ∀ v ∈ U.erase a, ∃ hn : v.toNode.1.2 ≠ [], GNode.parent v.toNode hn ∈ U := fun v hv =>
      cl_realization_parent hB R v.toNode ((branch_mem_clRealizationNodes v).mpr (Finset.mem_of_mem_erase hv))
        (fun h => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective h))
    have hR : ∏ v ∈ clInteriorBranches R, treeNorm c D hG layer hLayer v =
        ∏ x ∈ (U.erase a) ×ˢ (Finset.univ : Finset Bool), nodeNorm D hG layer hLayer c x.1.toNode := by
      rw [Finset.prod_product]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Fintype.prod_bool, nodeNorm_branch_sq D hG layer hLayer c hc]
    rw [hR]
    symm
    refine Finset.prod_bij (fun x hx => (.inl (⟨x.1, (hpar x.1 (Finset.mem_product.mp hx).1).fst⟩, x.2) : GardenDart G))
      ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hn, hp⟩ := hpar x.1 (Finset.mem_product.mp hx).1
      have hu := Finset.mem_of_mem_erase (Finset.mem_product.mp hx).1
      refine Finset.mem_filter.mpr ⟨mem_regionDarts.mpr ?_, rfl⟩
      rcases x with ⟨v, s⟩
      cases s
      · exact ⟨hu, hp⟩
      · exact ⟨hp, hu⟩
    · intro x _ y _ h
      simp only [Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Prod.ext (congrArg Subtype.val h.1) h.2
    · intro y hy
      obtain ⟨hyU, hyl⟩ := Finset.mem_filter.mp hy
      rcases y with ⟨cc, s⟩ | l
      · have hg := mem_regionDarts.mp hyU
        have hcU : cc.1 ∈ U ∧ GNode.parent cc.1.toNode cc.2 ∈ U := by
          cases s
          · exact ⟨hg.1, hg.2⟩
          · exact ⟨hg.2, hg.1⟩
        have hca : cc.1 ≠ a := by
          intro h
          apply R.parentPattern.1
          subst h
          exact ⟨cc.2, hcU.2⟩
        exact ⟨(cc.1, s), Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hca, hcU.1⟩, Finset.mem_univ _⟩, rfl⟩
      · exact absurd hyl (by simp)
    · intro x _
      rfl

end

end WaveTurbulence.Flower.V5WB
